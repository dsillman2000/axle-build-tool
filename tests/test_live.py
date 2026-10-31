"""Live regression tests against the real Axle API.

These exercise the demos end-to-end through the real entry point with a
real `AxleClient` — no fakes — so regressions in payload assembly,
environment handling, or the SDK wiring surface against the actual
service. They are marked `live` and skipped unless `AXLE_API_KEY` is
set; CI (offline) never runs them. Run explicitly with:

    AXLE_API_KEY=... uv run pytest -m live

Each test copies its demo fixture to a temporary directory so a live
run never leaves `.axbt/` state in the repository.
"""

from __future__ import annotations

import asyncio
import os
import shutil
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

DEMO_NAMES = ("RootTwoIrrational", "GaussIntSum")

#: Expected extracted declarations per demo file (the fully proved
#: targets the demos ship with).
EXPECTED_DECLS = {
    "RootTwoIrrational": {
        "Divisibility": {"prime_gt_one", "prime_dvd_square"},
        "EuclidLemma": {"euclid_lemma"},
        "IrrationalSqrtTwo": {"sqrt_two_irrational"},
    },
    "GaussIntSum": {"GaussSum": {"gauss_sum_identity"}},
}


@pytest.fixture
def in_demo(tmp_path: Path, demos_dir: Path, monkeypatch):
    """Copy a demo to tmp, chdir into it, yield the project root."""
    def _enter(name: str) -> Path:
        root = tmp_path / name
        shutil.copytree(demos_dir / name, root)
        monkeypatch.chdir(root)
        return root

    return _enter


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
                return await service._effective_environment()

        resolved = asyncio.run(probe())
        assert resolved.startswith("lean-"), resolved


class TestLiveDemoCompile:
    @pytest.mark.parametrize("demo_name", DEMO_NAMES)
    def test_compile_extracts_expected_declarations(
        self, in_demo, demo_name: str
    ) -> None:
        """`axbt compile` against the real API enriches every node."""
        root = in_demo(demo_name)
        result = runner.invoke(main, ["compile"])
        assert result.exit_code == 0, result.output

        from axle_build_tool.manifest import load_manifest

        manifest = load_manifest(root)
        assert manifest.nodes, "no nodes compiled"
        for node in manifest.nodes:
            # A successful compile records every node as clean (the
            # source-diff status is computed after the build).
            assert node.status == "clean"
            expected = EXPECTED_DECLS[demo_name][node.name.split(".")[-1]]
            extracted = {decl.name for decl in node.declarations}
            assert expected <= extracted, (node.name, extracted)
            # The demos are fully proved: no sorry anywhere.
            assert not any(decl.is_sorry for decl in node.declarations)

    def test_recompile_marks_everything_clean(self, in_demo) -> None:
        """§3's incremental promise holds against the live API."""
        root = in_demo("RootTwoIrrational")
        assert runner.invoke(main, ["compile"]).exit_code == 0
        result = runner.invoke(main, ["compile"])
        assert result.exit_code == 0, result.output
        assert "Nothing to extract" in result.output or "clean" in result.output

        from axle_build_tool.manifest import load_manifest

        manifest = load_manifest(root)
        assert all(node.status == "clean" for node in manifest.nodes)

    def test_no_import_project_extracts_declarations(self, tmp_path, monkeypatch) -> None:
        """Regression: files with no import lines extract declarations.

        There was a time when every document was silently dropped for
        such files (an off-by-one in the reported position semantics),
        leaving `declarations: []` in the manifest and a confusing
        "no declarations were extracted" error from `check`.
        """
        root = tmp_path / "proj"
        (root / "M").mkdir(parents=True)
        (root / "axbt_project.yml").write_text(
            "project:\n  name: proj\nmodules:\n  M:\n    targets:\n      - A.t1\n",
            encoding="utf-8",
        )
        (root / "M" / "A.lean").write_text(
            "theorem t1 : 1 = 1 := rfl\n\ntheorem t2 : 2 = 1 + 1 := rfl\n",
            encoding="utf-8",
        )
        monkeypatch.chdir(root)

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

    def test_compile_failure_reports_the_broken_file(self, in_demo, tmp_path) -> None:
        """A Lean error in a source fails compile with file context."""
        root = in_demo("RootTwoIrrational")
        (root / "RootTwoIrrational" / "Broken.lean").write_text(
            "import Mathlib\n\ntheorem broken : False := by rfl\n",
            encoding="utf-8",
        )
        result = runner.invoke(main, ["compile"])
        assert result.exit_code == 1, result.output
        assert "Broken.lean" in result.output
        # The previous manifest is untouched by the failed run.
        from axle_build_tool.manifest import MANIFEST_VERSION, load_manifest

        if (root / ".axbt" / "manifest.json").exists():
            assert load_manifest(root).version == MANIFEST_VERSION


class TestLiveDemoCheck:
    def test_check_demo_targets_all_okay(self, in_demo) -> None:
        """The full compile-then-check ritual passes on the live API."""
        in_demo("RootTwoIrrational")
        assert runner.invoke(main, ["compile"]).exit_code == 0
        result = runner.invoke(main, ["check"])
        assert result.exit_code == 0, result.output
        assert result.output.count("  OK") == 3
        assert "Checked 3 selection(s): all OK" in result.output

    def test_check_gauss_demo_target(self, in_demo) -> None:
        in_demo("GaussIntSum")
        assert runner.invoke(main, ["compile"]).exit_code == 0
        result = runner.invoke(main, ["check"])
        assert result.exit_code == 0, result.output
        assert (
            status_line(result.output, "GaussIntSum.GaussSum.gauss_sum_identity")
            == "GaussIntSum.GaussSum.gauss_sum_identity OK"
        )

    def test_check_declaration_selection(self, in_demo) -> None:
        """A declaration-level selection checks in full dependency context."""
        in_demo("RootTwoIrrational")
        assert runner.invoke(main, ["compile"]).exit_code == 0
        result = runner.invoke(
            main, ["check", "--select", "RootTwoIrrational.EuclidLemma.euclid_lemma"]
        )
        assert result.exit_code == 0, result.output
        assert (
            status_line(result.output, "RootTwoIrrational.EuclidLemma.euclid_lemma")
            == "RootTwoIrrational.EuclidLemma.euclid_lemma OK"
        )

    def test_check_failure_exits_1_with_messages(self, in_demo) -> None:
        """A source corrupted after compile fails check with attribution."""
        root = in_demo("RootTwoIrrational")
        assert runner.invoke(main, ["compile"]).exit_code == 0
        # Corrupt the *targeted declaration itself*: check submits the
        # current sources with `names=[declaration]` focusing, so errors
        # outside the named declarations are (correctly) not reported.
        # `--no-compile` is required to reach check's own failure path:
        # the default precursor compile would fail first (a corrupted
        # source cannot be extracted cleanly either).
        divisibility = root / "RootTwoIrrational" / "Divisibility.lean"
        source = divisibility.read_text(encoding="utf-8")
        assert "hp.one_lt" in source
        divisibility.write_text(
            source.replace("hp.one_lt", "hp.nonexistent_property"),
            encoding="utf-8",
        )
        result = runner.invoke(main, ["check", "--no-compile"])
        assert result.exit_code == 1, result.output
        assert "FAIL" in result.output
        # The Lean error is attributed back to the user's file.
        assert "Divisibility.lean" in result.output

    def test_check_recompiles_a_corrupted_source_by_default(self, in_demo) -> None:
        """The default precursor compile fails fast with file context."""
        root = in_demo("RootTwoIrrational")
        assert runner.invoke(main, ["compile"]).exit_code == 0
        divisibility = root / "RootTwoIrrational" / "Divisibility.lean"
        source = divisibility.read_text(encoding="utf-8")
        divisibility.write_text(
            source.replace("hp.one_lt", "hp.nonexistent_property"),
            encoding="utf-8",
        )

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 1, result.output
        # The failure is the precursor's extraction, reported against the
        # user's file — not an unchecked stale selection.
        assert "Failed to extract declarations" in result.output
        assert "Divisibility.lean" in result.output

    def test_full_refresh_reextracts_and_rechecks_unchanged_files(
        self, in_demo
    ) -> None:
        """--full-refresh on a clean tree: everything re-extracted and
        re-checked, even though nothing changed."""
        in_demo("RootTwoIrrational")
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check", "--full-refresh"])

        assert result.exit_code == 0, result.output
        assert "3 new, 0 changed, 0 clean" in result.output
        assert result.output.count("  OK") == 3
        assert "Checked 3 selection(s): all OK" in result.output


class TestLiveDemoVerify:
    def test_verify_demo_targets_all_okay(self, in_demo) -> None:
        """The demo theorems survive kernel-level verification."""
        in_demo("RootTwoIrrational")
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        assert result.output.count("  OK") == 3
        assert "Verified 3 selection(s): all OK" in result.output

    def test_verify_rejects_sorried_and_axiom_proofs(self, tmp_path, monkeypatch) -> None:
        """Elaborating-but-incomplete proofs fail verification."""
        root = tmp_path / "proj"
        (root / "M").mkdir(parents=True)
        (root / "axbt_project.yml").write_text(
            "project:\n  name: proj\nmodules:\n  M:\n    targets:\n      - A.holds\n"
            "      - A.uses_axiom\n",
            encoding="utf-8",
        )
        (root / "M" / "A.lean").write_text(
            "theorem holds : 1 + 1 = 2 := rfl\n\n"
            "axiom magic : 2 + 2 = 5\n\n"
            "theorem uses_axiom : 2 + 2 = 5 := magic\n",
            encoding="utf-8",
        )
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 1, result.output
        assert status_line(result.output, "M.A.holds") == "M.A.holds OK"
        assert status_line(result.output, "M.A.uses_axiom") == "M.A.uses_axiom FAIL"
        assert "failed declarations: uses_axiom" in result.output


class TestLiveEnvironmentValidation:
    def test_unknown_pinned_environment_fails_with_hint(self, tmp_path, monkeypatch) -> None:
        """Decision 2: a bogus pinned env fails compile with the names."""
        root = tmp_path / "proj"
        root.mkdir()
        (root / "axbt_project.yml").write_text(
            "project:\n  name: proj\nmodules:\n  M:\n    targets: []\n"
            "axle:\n  environment: lean-9.9.9\n",
            encoding="utf-8",
        )
        (root / "M").mkdir()
        (root / "M" / "A.lean").write_text("def t1 := 1\n", encoding="utf-8")
        monkeypatch.chdir(root)
        result = runner.invoke(main, ["compile"])
        assert result.exit_code == 1, result.output
        assert "lean-9.9.9" in result.output
        assert "available" in result.output
