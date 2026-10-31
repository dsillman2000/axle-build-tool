"""CLI-level tests for `axbt check`, driven through the real entry point."""

from __future__ import annotations

from pathlib import Path

from axle.types import CheckResponse, Messages
from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.manifest import load_manifest, manifest_path
from conftest import make_document, make_response, status_line

runner = CliRunner()

TARGETS_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets:
      - A.t1
      - B.t2
"""

NO_TARGETS_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""


def pinned_config(environment: str) -> str:
    return (
        "project:\n"
        "  name: proj\n"
        "modules:\n"
        "  M:\n"
        "    targets:\n"
        "      - A.t1\n"
        "axle:\n"
        f'  environment: "{environment}"\n'
    )


TWO_FILES = {"M/A.lean": "def t1 := 1\n", "M/B.lean": "import A\ndef t2 := t1\n"}

# Extraction documents matching the two-file project above: `t1` lives in
# A (payload line 1); `t2` in B, whose section starts at payload line 3
# (A's single line is inlined first, then a blank separator). Positions
# are one-based payload coordinates, as the API reports them.
TWO_FILE_DOCS = {
    "def t1 := 1": {"t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1)},
    "def t2 := t1": {"t2": make_document("t2", kind="def", line_pos=3, end_line_pos=3)},
}


def check_calls(fake_axle) -> list[dict]:
    return [kwargs for method, kwargs in fake_axle.calls if method == "check"]


class TestTargetsDefault:
    def test_bare_check_checks_every_configured_target(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 0, result.output
        # Auto-selected environment (no ping validation needed), then one
        # check call per configured target.
        methods = [method for method, _ in fake_axle.calls]
        assert methods == ["get_latest_environment", "check", "check"]
        first, second = check_calls(fake_axle)
        # Each target is a standalone payload: dependencies are inlined,
        # the target's own section is present, unrelated files are not.
        assert "def t1 := 1" in first["content"]
        assert "def t2 := t1" not in first["content"]
        assert "def t1 := 1" in second["content"]
        assert "def t2 := t1" in second["content"]
        # Declaration-level targets focus the check on their declaration.
        assert first["names"] == ["t1"]
        assert second["names"] == ["t2"]
        assert status_line(result.output, "M.A.t1") == "M.A.t1 OK"
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"
        assert "Checked 2 selection(s): all OK" in result.output

    def test_duplicate_targets_are_deduplicated(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        config = TARGETS_CONFIG.replace("      - B.t2\n", "      - A.t1\n")
        root = make_project(tmp_path, config, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 0, result.output
        assert len(check_calls(fake_axle)) == 1
        assert "Checked 1 selection(s): all OK" in result.output

    def test_no_targets_reports_nothing_and_makes_no_api_calls(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "def t1 := 1": {
                "t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1)
            }
        }
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 0, result.output
        assert "No targets configured" in result.output
        assert fake_axle.calls == []


class TestSelection:
    def test_declaration_selection_submits_its_payload_with_names(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check", "--select", "M.B.t2"])

        assert result.exit_code == 0, result.output
        calls = check_calls(fake_axle)
        assert len(calls) == 1
        # The declaration is named (its full extracted name), and the
        # payload carries the dependency's source.
        assert calls[0]["names"] == ["t2"]
        assert "def t1 := 1" in calls[0]["content"]
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"
        assert "Checked 1 selection(s): all OK" in result.output

    def test_module_selection_checks_everything_in_one_call(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check", "--select", "M"])

        assert result.exit_code == 0, result.output
        calls = check_calls(fake_axle)
        assert len(calls) == 1
        assert calls[0]["names"] is None
        assert "def t1 := 1" in calls[0]["content"]
        assert "def t2 := t1" in calls[0]["content"]
        assert status_line(result.output, "M") == "M OK"


class TestFailureReporting:
    def test_failure_prints_attributed_messages_and_exits_1(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(
            tmp_path,
            NO_TARGETS_CONFIG,
            {"M/A.lean": "import Mathlib\ndef t1 := 1\ndef broken := x\n"},
        )
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "def broken := x": {
                "broken": make_document("broken", kind="def", line_pos=4, end_line_pos=4)
            }
        }
        assert runner.invoke(main, ["compile"]).exit_code == 0
        # Payload line 4 (`def broken := x`) is source line 3; the hoisted
        # import header occupies payload line 1.
        fake_axle.check_result = make_response(
            CheckResponse,
            okay=False,
            lean_messages=Messages(
                ["-:4:15: error: unknown identifier 'x'", "-:1:1: error: header trouble"],
                [],
                [],
            ),
        )

        result = runner.invoke(main, ["check", "--select", "M.A"])

        assert result.exit_code == 1
        assert status_line(result.output, "M.A") == "M.A FAIL"
        # Positions are attributed back to the real source file...
        assert "    M/A.lean:3:15: error: unknown identifier 'x'" in result.output
        # ...while positions with no source counterpart are left alone.
        assert "    -:1:1: error: header trouble" in result.output
        assert "Checked 1 selection(s): 1 failed, 0 OK" in result.output

    def test_okay_response_with_warnings_still_succeeds(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "def t1 := 1": {
                "t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1)
            }
        }
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.check_result = make_response(
            CheckResponse,
            okay=True,
            lean_messages=Messages([], ["-:1:4: warning: unused variable"], []),
        )

        result = runner.invoke(main, ["check", "--select", "M.A"])

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.A") == "M.A OK"
        assert "    M/A.lean:1:4: warning: unused variable" in result.output

    def test_failure_without_lean_messages_reports_failed_declarations(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "def t1 := 1": {
                "t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1)
            }
        }
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.check_result = make_response(
            CheckResponse, okay=False, failed_declarations=["t1"]
        )

        result = runner.invoke(main, ["check", "--select", "M.A"])

        assert result.exit_code == 1
        assert "failed declarations: t1" in result.output


class TestPlanErrors:
    def test_dangling_target_fails_with_guidance(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        config = TARGETS_CONFIG.replace("      - B.t2\n", "      - B.nope\n")
        root = make_project(tmp_path, config, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 1
        assert "declaration 'nope' not found" in result.output
        assert "M/B.lean" in result.output

    def test_unknown_select_module_fails_with_guidance(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check", "--select", "Nope"])

        assert result.exit_code == 1
        assert "Unknown module 'Nope'" in result.output

    def test_no_compile_without_manifest_fails_with_compile_hint(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["check", "--no-compile"])

        assert result.exit_code != 0
        assert "compile" in result.output


class TestCompilePrecursor:
    """`check` compiles by default so the manifest is never stale."""

    def test_check_compiles_first_when_the_manifest_is_missing(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 0, result.output
        assert manifest_path(root).is_file()
        # Extraction happened as part of the precursor compile, then the
        # per-target checks ran.
        assert len([m for m, _ in fake_axle.calls if m == "extract_decls"]) == 2
        assert len(check_calls(fake_axle)) == 2
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"

    def test_check_recompiles_changed_sources_by_default(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        # A new declaration the manifest knows nothing about: the default
        # check recompiles (re-extracting the changed file) and succeeds.
        (root / "M/B.lean").write_text(
            "import A\ndef t2 := t1\ndef t3 := t2\n", encoding="utf-8"
        )
        # B's re-extraction now reports both defs (one-based payload
        # coordinates; B's section starts at payload line 3).
        fake_axle._extract_documents_by_marker["def t3 := t2"] = {
            "t2": make_document("t2", kind="def", line_pos=3, end_line_pos=3),
            "t3": make_document("t3", kind="def", line_pos=4, end_line_pos=4),
        }

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 0, result.output
        assert len([m for m, _ in fake_axle.calls if m == "extract_decls"]) == 1
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"
        extracted = load_manifest(root).by_name()["M.B"].declarations
        assert [d.name for d in extracted] == ["t2", "t3"]

    def test_no_compile_takes_the_manifest_at_face_value(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        # The source changes after compiling; --no-compile must not
        # re-extract (the manifest is taken at face value).
        (root / "M/B.lean").write_text(
            "import A\ndef t2 := t1\ndef t3 := t2\n", encoding="utf-8"
        )

        result = runner.invoke(main, ["check", "--no-compile"])

        assert result.exit_code == 0, result.output
        assert not [m for m, _ in fake_axle.calls if m == "extract_decls"]
        assert len(check_calls(fake_axle)) == 2

    def test_clean_compile_makes_no_api_calls_even_when_pinned(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """An incremental compile of a clean tree stays fully offline —
        even environment validation is skipped (nothing to submit)."""
        root = make_project(tmp_path, pinned_config("lean-4.35.0"), TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert fake_axle.calls == []


class TestRunModes:
    """--full-refresh ignores the manifest's carry-over entirely."""

    def test_full_refresh_compile_reextracts_everything(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["compile", "--full-refresh"])

        assert result.exit_code == 0, result.output
        # Nothing changed, yet every file was re-extracted.
        assert len([m for m, _ in fake_axle.calls if m == "extract_decls"]) == 2
        assert "2 new, 0 changed, 0 clean" in result.output
        assert "Extraction: 2 extracted now, 0 carried over" in result.output

    def test_full_refresh_check_reextracts_and_rechecks_unchanged_files(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """The user-facing promise: even on a clean tree, --full-refresh
        re-compiles and re-checks everything."""
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check", "--full-refresh"])

        assert result.exit_code == 0, result.output
        assert len([m for m, _ in fake_axle.calls if m == "extract_decls"]) == 2
        assert len(check_calls(fake_axle)) == 2
        assert status_line(result.output, "M.A.t1") == "M.A.t1 OK"
        assert "Checked 2 selection(s): all OK" in result.output

    def test_explicit_incremental_matches_the_default(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check", "--incremental"])

        assert result.exit_code == 0, result.output
        # Clean tree: the incremental precursor makes no API calls.
        assert [m for m, _ in fake_axle.calls if m == "extract_decls"] == []
        assert len(check_calls(fake_axle)) == 2

    def test_full_refresh_conflicts_with_no_compile(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check", "--full-refresh", "--no-compile"])

        assert result.exit_code != 0
        assert "conflicts with --no-compile" in result.output


class TestEnvironmentValidation:
    def test_unknown_pinned_environment_fails_fast_with_hint(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, pinned_config("lean-4.35.0"), TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        # The environment goes bad after compiling (e.g. the config was
        # edited, or the API stopped serving it).
        (root / "axbt_project.yml").write_text(
            pinned_config("lean-4.35.1"), encoding="utf-8"
        )
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 1
        assert "Did you mean 'lean-4.35.0'?" in result.output
        # Nothing was submitted: validation fails before any check call.
        assert check_calls(fake_axle) == []

    def test_compile_also_validates_a_pinned_environment(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, pinned_config("lean-4.35.1"), TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._environments = [{"name": "lean-4.35.0"}]

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 1
        assert "Did you mean 'lean-4.35.0'?" in result.output
        # Nothing was extracted: validation fails before any submission.
        assert check_calls(fake_axle) == []
        assert not [call for call in fake_axle.calls if call[0] == "extract_decls"]

    def test_served_pinned_environment_proceeds(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, pinned_config("lean-4.35.0"), TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 0, result.output
        methods = [method for method, _ in fake_axle.calls]
        assert methods == ["environments", "check"]
        assert fake_axle.calls[0][1]["timeout_seconds"] == 120

    def test_auto_selected_environment_needs_no_validation(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        assert runner.invoke(main, ["check"]).exit_code == 0

        assert "environments" not in [method for method, _ in fake_axle.calls]


RITUAL_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets:
      - A.t1
      - B.t2
axle:
  environment: "lean-4.35.0"
  global_options:
    maxHeartbeats: 100000
"""


class TestSorry:
    """`--sorry <selector>`: stub dependency subtrees (plan §5)."""

    SORRY_FILES = {
        "M/A.lean": "def base := 1\ntheorem base_holds : base = 1 := rfl\n",
        "M/B.lean": "import A\ndef middle := base + 1\n",
        "M/C.lean": "import B\ntheorem top : middle = 2 := by decide\n",
    }
    SORRY_DOCS = {
        "def base := 1": {
            "base": make_document(
                "base", kind="def", line_pos=1, end_line_pos=1, signature="def base : Nat"
            ),
            "base_holds": make_document(
                "base_holds",
                kind="theorem",
                line_pos=2,
                end_line_pos=2,
                signature="theorem base_holds : base = 1",
            ),
        },
        "def middle := base + 1": {
            "middle": make_document(
                "middle", kind="def", line_pos=4, end_line_pos=4, signature="def middle : Nat"
            ),
        },
        "theorem top": {
            "top": make_document(
                "top",
                kind="theorem",
                line_pos=6,
                end_line_pos=6,
                signature="theorem top : middle = 2",
            ),
        },
    }

    def compile_chain(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> Path:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, self.SORRY_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.SORRY_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        return root

    def test_sorry_stubs_the_dependency_subtree(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(main, ["check", "--select", "M.C", "--sorry", "M.A"])

        assert result.exit_code == 0, result.output
        content = check_calls(fake_axle)[0]["content"]
        # A's bodies are stubbed (signatures preserved)...
        assert "def base : Nat := sorry" in content
        assert "theorem base_holds : base = 1 := by sorry" in content
        # ...B (not stubbed) is real...
        assert "def middle := base + 1" in content
        # ...and the selection is never stubbed.
        assert "theorem top : middle = 2 := by decide" in content
        # The submitted payload is persisted for inspection.
        persisted = root / ".axbt" / "compiled" / "M_C_stubbed.lean"
        assert persisted.is_file()
        assert persisted.read_text(encoding="utf-8") == content

    def test_sorry_is_repeatable(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(
            main, ["check", "--select", "M.C", "--sorry", "M.A", "--sorry", "M.B"]
        )

        assert result.exit_code == 0, result.output
        content = check_calls(fake_axle)[0]["content"]
        assert "def base : Nat := sorry" in content
        assert "def middle : Nat := sorry" in content
        assert "theorem top : middle = 2 := by decide" in content

    def test_sorry_declaration_level_stubs_one_declaration(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(
            main, ["check", "--select", "M.C", "--sorry", "M.A.base"]
        )

        assert result.exit_code == 0, result.output
        content = check_calls(fake_axle)[0]["content"]
        assert "def base : Nat := sorry" in content
        assert "theorem base_holds : base = 1 := rfl" in content  # sibling stays real

    def test_sorry_rejects_non_dependencies(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(
            main, ["check", "--select", "M.A", "--sorry", "M.C"]
        )

        assert result.exit_code == 1
        assert "not a dependency of 'M.A'" in result.output

    def test_sorry_rejects_the_selection_itself(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(
            main, ["check", "--select", "M.A", "--sorry", "M.A"]
        )

        assert result.exit_code == 1
        assert "never stubbed" in result.output

    def test_sorry_rejects_targets_inside_the_stubbed_subtree(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        config = NO_TARGETS_CONFIG.replace("targets: []", "targets:\n      - B.middle")
        root = make_project(tmp_path, config, self.SORRY_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.SORRY_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check", "--sorry", "M.B"])

        assert result.exit_code == 1
        assert "never stubbed" in result.output
        assert check_calls(fake_axle) == []

    def test_sorry_on_own_file_stubs_siblings_for_declaration_selections(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """`--select M.A.base_holds --sorry M.A`: stub my siblings, judge
        me — the selected declaration keeps its real body."""
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(
            main, ["check", "--select", "M.A.base_holds", "--sorry", "M.A"]
        )

        assert result.exit_code == 0, result.output
        content = check_calls(fake_axle)[0]["content"]
        assert "def base : Nat := sorry" in content  # sibling stubbed
        assert "theorem base_holds : base = 1 := rfl" in content  # selection real

    def test_sorry_naming_only_the_selected_declaration_is_rejected(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(
            main, ["check", "--select", "M.A.base_holds", "--sorry", "M.A.base_holds"]
        )

        assert result.exit_code == 1
        assert "never stubbed" in result.output

    def test_sorry_on_own_module_is_rejected_for_module_selections(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(main, ["check", "--select", "M", "--sorry", "M.A"])

        assert result.exit_code == 1
        assert "never stubbed" in result.output

    def test_stale_manifest_warns_with_the_compile_prescription(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A `--no-compile` run against a file edited since compiling
        warns that stubs could not be applied — never silently."""
        root = self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)
        # Shift A's declarations down one line without recompiling.
        (root / "M/A.lean").write_text(
            "-- a new comment line\ndef base := 1\n"
            "theorem base_holds : base = 1 := rfl\n",
            encoding="utf-8",
        )

        result = runner.invoke(
            main, ["check", "--select", "M.C", "--sorry", "M.A", "--no-compile"]
        )

        assert result.exit_code == 0, result.output  # warns, does not fail
        assert "warning:" in result.output
        assert "M/A.lean" in result.output
        assert "could not be stubbed" in result.output
        assert "run `axbt compile`" in result.output
        # The un-stubbable code stayed real in the payload.
        content = check_calls(fake_axle)[0]["content"]
        assert "def base := 1" in content


class TestRitual:
    def test_compile_then_check_ritual(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """The full offline ritual — compile then check every target —
        with the project's config plumbing reaching the API."""
        root = make_project(tmp_path, RITUAL_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS

        compile_result = runner.invoke(main, ["compile"])
        assert compile_result.exit_code == 0, compile_result.output
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 0, result.output
        assert result.output.count("  OK") == 2
        assert "Checked 2 selection(s): all OK" in result.output
        # The ritual is incremental: the clean compile makes no API
        # calls; the check validates the pinned environment, then its
        # submissions carry the config's global options.
        assert [method for method, _ in fake_axle.calls] == [
            "environments",
            "check",
            "check",
        ]
        assert check_calls(fake_axle)[0]["global_options"] == {"maxHeartbeats": 100000}

    def test_check_declaration_selection_ritual(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, RITUAL_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check", "--select", "M.B.t2"])

        assert result.exit_code == 0, result.output
        calls = check_calls(fake_axle)
        assert len(calls) == 1
        assert calls[0]["names"] == ["t2"]
        # The payload inlines the dependency.
        assert "def t1 := 1" in calls[0]["content"]
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"
