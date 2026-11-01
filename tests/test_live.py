"""Live regression tests against the real Axle API.

These drive the real CLI entry point with a real `AxleClient` — no
fakes — so regressions in payload assembly, environment handling, or
the SDK wiring surface against the actual service. They are marked
`live` and skipped unless `AXLE_API_KEY` is set; CI (offline) never
runs them. Run explicitly with:

    AXLE_API_KEY=... uv run pytest -m live

The suite is fully self-contained: every test builds its own ad-hoc
Lean project in a temporary directory. Nothing here depends on the
repository's `demos/` — those are exercised by the dedicated demo
workflows, not by this suite.
"""

from __future__ import annotations

import asyncio
import os
from pathlib import Path

import pytest
from click.testing import CliRunner

from axle_build_tool import main
from conftest import status_line

#: The live suite needs credentials; without them every test skips.
HAVE_API_KEY = bool(os.environ.get("AXLE_API_KEY"))

pytestmark = [
    pytest.mark.live,
    pytest.mark.skipif(
        not HAVE_API_KEY, reason="live tests require AXLE_API_KEY to be set"
    ),
]

runner = CliRunner()

#: The Lean environment the live suite pins (deterministic submissions).
LIVE_ENVIRONMENT = "lean-4.35.0"

#: A base file with a hoisted external import, a module docstring (so
#: positions only come out right if the keyword-snap attribution works),
#: and proved declarations at known file lines.
BASE_SOURCE = """\
import Mathlib

/-! Base definitions. -/

def base : Nat := 1

theorem base_holds : base = 1 := rfl
"""

#: A file importing its sibling: cross-file dependency in full context.
USER_SOURCE = """\
import Base

theorem derived_holds : base + 0 = 1 := by simp [base]
"""

#: Elaborates cleanly but is not a complete proof.
SORRY_SOURCE = """\
import Mathlib

theorem gap : 2 + 2 = 5 := by sorry
"""

#: Elaborates cleanly but relies on an axiom — incomplete by another door.
AXIOM_SOURCE = """\
import Mathlib

axiom magic : 2 + 2 = 5

theorem uses_axiom : 2 + 2 = 5 := magic
"""

#: A Lean error: fails elaboration, so compile (not check/verify) gates it.
BROKEN_SOURCE = """\
import Mathlib

theorem broken : False := by rfl
"""


@pytest.fixture
def make_live_project(tmp_path: Path, monkeypatch):
    """Build an ad-hoc Lean project and chdir into it.

    `files` maps module-relative paths to Lean sources; `targets` are
    the module-relative target selectors (default: none); pass
    `environment=None` to omit the pin (auto-select). Returns the
    project root.
    """
    import yaml

    def _make(
        files: dict[str, str],
        targets: list[str] | None = None,
        environment: str | None = LIVE_ENVIRONMENT,
    ) -> Path:
        root = tmp_path / "proj"
        (root / "M").mkdir(parents=True)
        for relative, content in files.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
        axle: dict = {"timeout_seconds": 120}
        if environment is not None:
            axle["environment"] = environment
        config = {
            "project": {"name": "proj"},
            "modules": {"M": {"targets": targets or []}},
            "axle": axle,
        }
        (root / "axbt_project.yml").write_text(
            yaml.safe_dump(config, sort_keys=False), encoding="utf-8"
        )
        monkeypatch.chdir(root)
        return root

    return _make


class TestLiveEnvironments:
    def test_environments_endpoint_lists_lean(self) -> None:
        """The API's environments endpoint is reachable and serves Lean."""
        from axle_build_tool.axle_service import AxleService
        from axle_build_tool.config import AxleConfig

        async def probe() -> list[str]:
            service = AxleService(AxleConfig())
            async with service:
                entries = await service.environments()
            return sorted(str(entry["name"]) for entry in entries)

        available = asyncio.run(probe())
        assert available, "the Axle API serves no environments"
        assert any(name.startswith("lean-") for name in available), available

    def test_auto_selected_default_environment_is_lean(self) -> None:
        """Without a pinned environment the service picks a lean-* env."""
        from axle_build_tool.axle_service import AxleService
        from axle_build_tool.config import AxleConfig

        async def probe() -> str:
            service = AxleService(AxleConfig())  # environment=None
            async with service:
                return await service.resolve_environment()

        resolved = asyncio.run(probe())
        assert resolved.startswith("lean-"), resolved


class TestLiveCompile:
    def test_compile_extracts_expected_declarations(self, make_live_project) -> None:
        """`axbt compile` against the real API enriches every node, with
        positions attributed to the declaring file's own coordinates."""
        root = make_live_project(
            {"M/Base.lean": BASE_SOURCE, "M/User.lean": USER_SOURCE},
            targets=["Base.base_holds", "User.derived_holds"],
        )

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        from axle_build_tool.manifest import load_manifest

        manifest = load_manifest(root)
        assert [node.name for node in manifest.nodes] == ["M.Base", "M.User"]
        base, user = manifest.by_name()["M.Base"], manifest.by_name()["M.User"]
        assert user.parents == ["M.Base"]  # the intra-project dependency

        base_decls = {decl.name: decl for decl in base.declarations}
        assert set(base_decls) == {"base", "base_holds"}
        # Positions point at the declaration keyword lines of the file.
        assert base_decls["base"].line_pos == 5
        assert base_decls["base_holds"].line_pos == 7
        assert base_decls["base"].kind == "def"
        assert base_decls["base_holds"].kind == "theorem"

        user_decls = {decl.name: decl for decl in user.declarations}
        assert set(user_decls) == {"derived_holds"}
        assert user_decls["derived_holds"].line_pos == 3

        for node in manifest.nodes:
            # A first compile extracts everything fresh (no previous
            # manifest): every node is "new" until the next compile
            # carries it as "clean".
            assert node.status == "new"
            assert node.declarations, f"{node.name} extracted nothing"
            # The sources are fully proved: no sorry anywhere.
            assert not any(decl.is_sorry for decl in node.declarations)

    def test_recompile_marks_everything_clean(self, make_live_project) -> None:
        """The incremental promise holds against the live API."""
        root = make_live_project({"M/Base.lean": BASE_SOURCE}, targets=["Base.base_holds"])
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert "0 new, 0 changed, 1 clean" in result.output
        from axle_build_tool.manifest import load_manifest

        assert all(node.status == "clean" for node in load_manifest(root).nodes)

    def test_no_import_project_extracts_declarations(self, make_live_project) -> None:
        """Regression: files with no import lines extract declarations.

        There was a time when every document was silently dropped for
        such files (an off-by-one in the reported position semantics),
        leaving `declarations: []` in the manifest and a confusing
        "no declarations were extracted" error from `check`.
        """
        root = make_live_project(
            {"M/A.lean": "theorem t1 : 1 = 1 := rfl\n\ntheorem t2 : 2 = 1 + 1 := rfl\n"},
            targets=["A.t1"],
        )

        result = runner.invoke(main, ["compile"])
        assert result.exit_code == 0, result.output

        from axle_build_tool.manifest import load_manifest

        node = load_manifest(root).by_name()["M.A"]
        extracted = {decl.name: decl for decl in node.declarations}
        assert set(extracted) == {"t1", "t2"}, extracted
        # Positions point at the declaration keyword lines in the file.
        assert extracted["t1"].line_pos == 1
        assert extracted["t2"].line_pos == 3

        check_result = runner.invoke(main, ["check"])
        assert check_result.exit_code == 0, check_result.output
        assert status_line(check_result.output, "M.A.t1") == "M.A.t1 OK"

    def test_compile_failure_reports_the_broken_file(self, make_live_project) -> None:
        """A Lean error in a source fails compile with file context."""
        root = make_live_project(
            {"M/Base.lean": BASE_SOURCE, "M/Broken.lean": BROKEN_SOURCE},
        )

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 1, result.output
        assert "Broken.lean" in result.output
        # The previous manifest is untouched by the failed run.
        from axle_build_tool.manifest import MANIFEST_VERSION, load_manifest

        if (root / ".axbt" / "manifest.json").exists():
            assert load_manifest(root).version == MANIFEST_VERSION


class TestLiveCheck:
    def test_check_targets_all_okay(self, make_live_project) -> None:
        """The full compile-then-check ritual passes on the live API."""
        make_live_project(
            {"M/Base.lean": BASE_SOURCE, "M/User.lean": USER_SOURCE},
            targets=["Base.base_holds", "User.derived_holds"],
        )
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 0, result.output
        assert result.output.count("  OK") == 2
        assert "Checked 2 selection(s): all OK" in result.output

    def test_check_declaration_selection(self, make_live_project) -> None:
        """A declaration-level selection checks in full dependency context."""
        make_live_project(
            {"M/Base.lean": BASE_SOURCE, "M/User.lean": USER_SOURCE},
        )
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check", "--select", "M.User.derived_holds"])

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.User.derived_holds") == (
            "M.User.derived_holds OK"
        )

    def test_check_failure_exits_1_with_messages(self, make_live_project) -> None:
        """A source corrupted after compile fails check with attribution."""
        root = make_live_project({"M/Base.lean": BASE_SOURCE}, targets=["Base.base_holds"])
        assert runner.invoke(main, ["compile"]).exit_code == 0
        # Corrupt the *targeted declaration itself*: check submits the
        # current sources with `names=[declaration]` focusing, so errors
        # outside the named declarations are (correctly) not reported.
        # `--no-compile` is required to reach check's own failure path:
        # the default precursor compile would fail first (a corrupted
        # source cannot be extracted cleanly either).
        base = root / "M" / "Base.lean"
        base.write_text(BASE_SOURCE.replace("= rfl", "= Hoff"), encoding="utf-8")

        result = runner.invoke(main, ["check", "--no-compile"])

        assert result.exit_code == 1, result.output
        assert "FAIL" in result.output
        # The Lean error is attributed back to the user's file.
        assert "Base.lean" in result.output

    def test_check_recompiles_a_corrupted_source_by_default(
        self, make_live_project
    ) -> None:
        """The default precursor compile fails fast with file context."""
        root = make_live_project({"M/Base.lean": BASE_SOURCE}, targets=["Base.base_holds"])
        assert runner.invoke(main, ["compile"]).exit_code == 0
        (root / "M" / "Base.lean").write_text(
            BASE_SOURCE.replace("= rfl", "= Hoff"), encoding="utf-8"
        )

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 1, result.output
        # The failure is the precursor's extraction, reported against the
        # user's file — not an unchecked stale selection.
        assert "Failed to extract declarations" in result.output
        assert "Base.lean" in result.output

    def test_full_refresh_reextracts_and_rechecks_unchanged_files(
        self, make_live_project
    ) -> None:
        """--full-refresh on a clean tree: everything re-extracted and
        re-checked, even though nothing changed."""
        make_live_project(
            {"M/Base.lean": BASE_SOURCE, "M/User.lean": USER_SOURCE},
            targets=["Base.base_holds", "User.derived_holds"],
        )
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check", "--full-refresh"])

        assert result.exit_code == 0, result.output
        assert "2 new, 0 changed, 0 clean" in result.output
        assert result.output.count("  OK") == 2
        assert "Checked 2 selection(s): all OK" in result.output


class TestLiveVerify:
    def test_verify_targets_all_okay(self, make_live_project) -> None:
        """Proved theorems survive kernel-level verification."""
        make_live_project(
            {"M/Base.lean": BASE_SOURCE, "M/User.lean": USER_SOURCE},
            targets=["Base.base_holds", "User.derived_holds"],
        )
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        assert result.output.count("  OK") == 2
        assert "Verified 2 selection(s): all OK" in result.output

    def test_verify_sorried_target_fails_locally(self, make_live_project) -> None:
        """A `sorry` target is judged without an API roundtrip."""
        make_live_project({"M/Gap.lean": SORRY_SOURCE}, targets=["Gap.gap"])
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 1, result.output
        assert status_line(result.output, "M.Gap.gap") == "M.Gap.gap FAIL"
        assert "declaration 'gap' has a `sorry`" in result.output

    def test_verify_rejects_axiom_proofs(self, make_live_project) -> None:
        """Elaborating-but-incomplete proofs fail verification."""
        make_live_project(
            {"M/Base.lean": BASE_SOURCE, "M/Axiom.lean": AXIOM_SOURCE},
            targets=["Base.base_holds", "Axiom.uses_axiom"],
        )
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 1, result.output
        assert status_line(result.output, "M.Base.base_holds") == "M.Base.base_holds OK"
        assert status_line(result.output, "M.Axiom.uses_axiom") == (
            "M.Axiom.uses_axiom FAIL"
        )
        assert "failed declarations: uses_axiom" in result.output


class TestLiveStubbing:
    """`--sorry`: iterate downstream against incomplete upstream code."""

    UPSTREAM = "theorem upstream : 1 + 1 = 2 := by sorry\n"

    def project(self, make_live_project) -> Path:
        return make_live_project(
            {
                "M/Base.lean": self.UPSTREAM,
                "M/User.lean": (
                    "import Base\n\ntheorem target : 1 + 1 = 2 := by simp [upstream]\n"
                ),
            },
            targets=["User.target"],
        )

    def test_verify_over_incomplete_upstream_needs_the_stub(self, make_live_project) -> None:
        """Upstream `sorry` fails verify by default; `--sorry` stubs and
        permits it, so the downstream theorem verifies."""
        self.project(make_live_project)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        without = runner.invoke(main, ["verify", "--select", "M.User"])
        assert without.exit_code == 1, without.output

        with_stub = runner.invoke(
            main, ["verify", "--select", "M.User", "--sorry", "M.Base"]
        )
        assert with_stub.exit_code == 0, with_stub.output
        assert status_line(with_stub.output, "M.User") == "M.User OK"

    def test_check_over_stubbed_upstream(self, make_live_project) -> None:
        """Check with stubbed upstream: the stubbed payload compiles
        standalone (signatures preserved) and the selection checks clean."""
        self.project(make_live_project)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(
            main, ["check", "--select", "M.User", "--sorry", "M.Base"]
        )

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.User.target") == "M.User.target OK"

    def test_stubbed_payload_is_persisted_for_inspection(
        self, make_live_project
    ) -> None:
        root = self.project(make_live_project)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        assert runner.invoke(
            main, ["verify", "--select", "M.User", "--sorry", "M.Base"]
        ).exit_code == 0

        persisted = root / ".axbt" / "compiled" / "M_User_stubbed.lean"
        assert persisted.is_file()
        content = persisted.read_text(encoding="utf-8")
        assert "theorem upstream : 1 + 1 = 2 := by sorry" in content
        assert "theorem target : 1 + 1 = 2 := by simp [upstream]" in content


class TestLiveScopedStatements:
    """Scope-correctness of verification, locked against regressions.

    verify's formal statements come from `theorem2sorry` — an in-place
    transform of the scope-complete payload — so namespaced, section,
    and variable-dependent declarations verify without any preamble
    assembly. These tests lock that property (a future change that
    assembles statements from bare signatures would fail here).
    """

    SCOPED = (
        "namespace Algebra\n"
        "variable (n : Nat)\n"
        "\n"
        "theorem gap : 2 + 2 = 5 := by sorry\n"
        "\n"
        "theorem helper : n = n := rfl\n"
        "\n"
        "def sibling : Nat := 1\n"
        "\n"
        "theorem uses_sibling : sibling = 1 := rfl\n"
        "\n"
        "end Algebra\n"
    )

    def test_verification_inside_namespaces_and_variables(self, make_live_project) -> None:
        """A declaration under `namespace` + `variable` verifies; a
        sorried sibling does not poison it."""
        make_live_project({"M/A.lean": self.SCOPED}, targets=["A.helper"])
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify", "--select", "M.A.helper"])

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.A.helper") == "M.A.helper OK"

    def test_stubbing_inside_a_namespace(self, make_live_project) -> None:
        """`--sorry` over a namespaced file: stubs replace the spans
        inside the namespace context and the payload still compiles."""
        make_live_project({"M/A.lean": self.SCOPED}, targets=["A.helper"])
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(
            main, ["verify", "--select", "M.A.helper", "--sorry", "M.A.gap"]
        )

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.A.helper") == "M.A.helper OK"

    def test_stubbing_own_file_siblings(self, make_live_project) -> None:
        """`--sorry` naming the selection's own node stubs its siblings;
        the selected declaration keeps its real proof."""
        make_live_project({"M/A.lean": self.SCOPED}, targets=["A.helper"])
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(
            main, ["verify", "--select", "M.A.helper", "--sorry", "M.A"]
        )

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.A.helper") == "M.A.helper OK"
        from pathlib import Path

        root = Path.cwd()
        persisted = root / ".axbt" / "compiled" / "M_A_stubbed.lean"
        content = persisted.read_text(encoding="utf-8")
        # The sibling and the sorried gap are stubbed inside the namespace...
        assert "theorem gap : 2 + 2 = 5 := by sorry" in content
        assert "theorem uses_sibling : sibling = 1 := by sorry" in content
        # ...and the selection's real proof survives.
        assert "theorem helper : n = n := rfl" in content


class TestLiveVerifyCache:
    """The verification cache: recorded per declaration, keyed on the
    file-closure content + environment + global options."""

    def test_second_verify_is_cached(self, make_live_project) -> None:
        make_live_project(
            {"M/Base.lean": BASE_SOURCE, "M/User.lean": USER_SOURCE},
            targets=["Base.base_holds", "User.derived_holds"],
        )
        assert runner.invoke(main, ["compile"]).exit_code == 0

        first = runner.invoke(main, ["verify"])
        assert first.exit_code == 0, first.output
        assert "(cached)" not in first.output

        second = runner.invoke(main, ["verify"])

        assert second.exit_code == 0, second.output
        assert second.output.count("(cached)") == 2
        assert "Verified 2 selection(s): all OK (2 cached)" in second.output

    def test_force_reverifies(self, make_live_project) -> None:
        make_live_project({"M/Base.lean": BASE_SOURCE}, targets=["Base.base_holds"])
        assert runner.invoke(main, ["verify"]).exit_code == 0

        result = runner.invoke(main, ["verify", "--force"])

        assert result.exit_code == 0, result.output
        assert "(cached)" not in result.output
        assert "Verified 1 selection(s): all OK" in result.output

    def test_dependency_edit_invalidates(self, make_live_project) -> None:
        root = make_live_project(
            {"M/Base.lean": BASE_SOURCE, "M/User.lean": USER_SOURCE},
            targets=["User.derived_holds"],
        )
        assert runner.invoke(main, ["verify"]).exit_code == 0

        # Touch Base (the dependency): the closure signature changes.
        (root / "M" / "Base.lean").write_text(
            BASE_SOURCE + "\n-- touched\n", encoding="utf-8"
        )

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        assert "(cached)" not in result.output
        assert "Verified 1 selection(s): all OK" in result.output


class TestLiveEnvironmentValidation:
    def test_unknown_pinned_environment_fails_with_hint(
        self, make_live_project
    ) -> None:
        """A bogus pinned env fails compile with the available names."""
        root = make_live_project(
            {"M/A.lean": "def t1 := 1\n"}, environment="lean-9.9.9"
        )

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 1, result.output
        assert "lean-9.9.9" in result.output
        assert "available" in result.output

    def test_permitted_sorries_excuse_a_sorried_declaration(
        self, make_live_project
    ) -> None:
        """The flag's names are matched qualified (observed live)."""
        make_live_project(
            {"M/Gap.lean": SORRY_SOURCE}, targets=["Gap.gap"],
        )
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(
            main, ["verify", "--permitted-sorries", "M.Gap.gap"]
        )

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.Gap.gap") == "M.Gap.gap SKIP"
        assert "excused (--permitted-sorries)" in result.output
        assert "Verified 1 selection(s): all OK, 1 skipped" in result.output


class TestLiveShare:
    def test_check_share_mints_a_real_link(self, make_live_project) -> None:
        """--share mints a platform share link for the submission."""
        base_url = os.environ.get("AXLE_API_URL", "https://axle.axiommath.ai").rstrip(
            "/"
        )
        make_live_project(
            {"M/Base.lean": BASE_SOURCE, "M/User.lean": USER_SOURCE},
            targets=["User.derived_holds"],
        )
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check", "--select", "M.User", "--share"])

        assert result.exit_code == 0, result.output
        assert f"share: {base_url}/check#r=" in result.output
        assert "Share link(s) minted: 1" in result.output


class TestLiveTierSplit:
    """Check and verify are genuinely distinct verdict tiers, and the
    manifest records both independently.

    A `sorry` elaborates with only a warning, so it passes the check
    tier while its kernel-level verification fails — locally, without
    an API call. The declaration ends up *checked-clean but
    unverified*: exactly the state #22's graph needs for the
    yellow/orange split, and impossible to express with a single
    `verified_*` stamp.
    """

    def test_sorried_theorem_checks_clean_but_fails_verification(
        self, make_live_project
    ) -> None:
        root = make_live_project({"M/Gap.lean": SORRY_SOURCE}, targets=["Gap.gap"])
        assert runner.invoke(main, ["compile"]).exit_code == 0

        check_result = runner.invoke(main, ["check", "--select", "M.Gap"])
        assert check_result.exit_code == 0, check_result.output
        assert "Recorded 1 check stamp(s) in the manifest" in check_result.output

        verify_result = runner.invoke(main, ["verify"])
        assert verify_result.exit_code == 1
        assert status_line(verify_result.output, "M.Gap.gap") == "M.Gap.gap FAIL"
        assert "declaration 'gap' has a `sorry`" in verify_result.output

        from axle_build_tool.manifest import load_manifest

        (gap,) = [
            decl
            for node in load_manifest(root).nodes
            for decl in node.declarations
        ]
        assert gap.checked_sig is not None
        assert gap.checked_at is not None
        assert gap.checked_request_id is not None
        # The failing verify recorded nothing — checked-clean and
        # unverified coexist on this one declaration.
        assert gap.verified_sig is None
        assert gap.verified_at is None

    def test_both_tiers_proven_declaration_holds_both_stamps(
        self, make_live_project
    ) -> None:
        root = make_live_project({"M/Base.lean": BASE_SOURCE}, targets=["Base.base_holds"])
        assert runner.invoke(main, ["compile"]).exit_code == 0

        assert runner.invoke(main, ["check"]).exit_code == 0
        assert runner.invoke(main, ["verify"]).exit_code == 0

        from axle_build_tool.manifest import load_manifest

        (base_holds,) = [
            decl
            for node in load_manifest(root).nodes
            for decl in node.declarations
        ]
        assert base_holds.checked_sig is not None
        assert base_holds.verified_sig is not None
        assert base_holds.checked_sig == base_holds.verified_sig
        assert base_holds.checked_request_id != base_holds.verified_request_id


class TestLiveDependencyNames:
    """The dependency names recorded per declaration are the graph's
    edges (#22): they must match how axbt extracts the declarations
    themselves, across files, with the dependency closure stubbed to
    signatures.

    Names in `dependencies` surface from the submitted extraction
    payload, whose dependency closure is signature-stubbed
    (`build_file_payload(..., stub_dependencies=True)`) — this probe
    exists to confirm the reported names are recognized against the
    extracted names (bare vs. qualified), that cross-file
    dependencies are reported at all, and that signature-stubbed
    dependency declarations still appear in the lists.
    """

    DEP_BASE = (
        "import Mathlib\n\n"
        "def shared : Nat := 1\n\n"
        "theorem shared_holds : shared = 1 := rfl\n"
    )
    DEP_USER = (
        "import Base\n\n"
        "namespace Scoped\n\n"
        "def combined : Nat := shared + 1\n\n"
        "theorem combined_holds : combined = 2 := rfl\n\n"
        "end Scoped\n"
    )

    def test_recorded_dependencies_match_extracted_names(
        self, make_live_project
    ) -> None:
        root = make_live_project({"M/Base.lean": self.DEP_BASE, "M/User.lean": self.DEP_USER})
        assert runner.invoke(main, ["compile"]).exit_code == 0

        from axle_build_tool.manifest import load_manifest

        manifest = load_manifest(root)
        extracted = {decl.name for node in manifest.nodes for decl in node.declarations}
        extracted_last_segments = {name.rsplit(".", 1)[-1] for name in extracted}
        user = manifest.by_name()["M.User"]
        user_decls = {decl.name.rsplit(".", 1)[-1]: decl for decl in user.declarations}
        assert {"combined", "combined_holds"} <= set(user_decls), extracted

        for decl in (d for node in manifest.nodes for d in node.declarations):
            # The union is deduplicated and sorted by construction.
            assert decl.dependencies == sorted(set(decl.dependencies))
            for dep in decl.dependencies:
                # Recognized: exact extracted name, or the bare
                # counterpart of one (Lean's namespacing means both
                # spellings can appear in the reported lists).
                assert (
                    dep in extracted or dep.rsplit(".", 1)[-1] in extracted_last_segments
                ), f"{decl.name}: unrecognized dependency {dep!r} (extracted: {sorted(extracted)})"

        # The cross-file edge: `combined := shared + 1` must name the
        # dependency in Base — reported even though Base's body was
        # signature-stubbed in User's extraction payload.
        combined = user_decls["combined"]
        assert combined.dependencies, f"no deps recorded: {combined}"
        assert any(dep.rsplit(".", 1)[-1] == "shared" for dep in combined.dependencies)
