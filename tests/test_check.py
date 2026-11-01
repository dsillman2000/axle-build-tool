"""CLI-level tests for `axbt check`, driven through the real entry point."""

from __future__ import annotations

import re
from pathlib import Path

from axle.types import CheckResponse, Messages
from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.config import load_config
from axle_build_tool.manifest import load_manifest, manifest_path
from conftest import checked_stamp_of, make_document, make_response, status_line

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
    "def t1 := 1": {"t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")},
    "def t2 := t1": {"t2": make_document("t2", kind="def", line_pos=3, end_line_pos=3, signature="def t2")},
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
        # Submissions stream in completion order, so identify calls by
        # their focused declaration rather than by log position.
        by_names = {c["names"][0]: c for c in check_calls(fake_axle)}
        first, second = by_names["t1"], by_names["t2"]
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
                "t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")
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
        # The module selection expands to per-declaration lines.
        assert status_line(result.output, "M.A.t1") == "M.A.t1 OK"
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"
        assert "Checked 1 selection(s): all OK" in result.output


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
                "broken": make_document(
                    "broken",
                    kind="def",
                    line_pos=4,
                    end_line_pos=4,
                    signature="def broken",
                )
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
        assert status_line(result.output, "M.A.broken") == "M.A.broken FAIL"
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
                "t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")
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
        assert status_line(result.output, "M.A.t1") == "M.A.t1 OK"
        assert "    M/A.lean:1:4: warning: unused variable" in result.output

    def test_failure_without_lean_messages_reports_failed_declarations(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, {"M/A.lean": "def t1 := 1\n"})
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "def t1 := 1": {
                "t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")
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
            "t2": make_document("t2", kind="def", line_pos=3, end_line_pos=3, signature="def t2"),
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
    """`--sorry <selector>`: stub dependency subtrees."""

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

    def test_sorry_applies_where_relevant_for_default_runs(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A bare run checks every target; a `--sorry` that is only a
        dependency of SOME of them applies where relevant and never
        errors for the rest (the Scoped-style targets don't depend on
        the stubbed file — nothing to stub there)."""
        config = NO_TARGETS_CONFIG.replace(
            "targets: []",
            "targets:\n      - B.middle\n      - C.top\n",
        )
        root = make_project(tmp_path, config, self.SORRY_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.SORRY_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check", "--sorry", "M.A"])

        assert result.exit_code == 0, result.output
        # B.middle's selection: A is its dependency -> stubbed.
        # C.top's selection: A is transitive -> stubbed too.
        assert len(check_calls(fake_axle)) == 2
        for call in check_calls(fake_axle):
            assert "def base : Nat := sorry" in call["content"]

    def test_sorry_nowhere_applicable_is_rejected(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A stub relevant to NO planned selection is a mistake."""
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(
            main, ["check", "--select", "M.A", "--sorry", "M.C"]
        )

        assert result.exit_code == 1
        assert "not a dependency of any planned selection" in result.output

    def test_sorry_selection_fully_granted_is_skipped(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """`--select M.A --sorry M.A`: the whole selection is taken as
        granted — reported SKIP, nothing submitted, exit 0."""
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(
            main, ["check", "--select", "M.A", "--sorry", "M.A"]
        )

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.A") == "M.A SKIP"
        assert "taken as granted (--sorry)" in result.output
        assert check_calls(fake_axle) == []

    def test_targets_inside_the_stubbed_subtree_are_skipped(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Config targets inside a `--sorry`'d subtree are taken as
        granted (skipped); the command line's grant wins for this run."""
        config = NO_TARGETS_CONFIG.replace("targets: []", "targets:\n      - B.middle")
        root = make_project(tmp_path, config, self.SORRY_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.SORRY_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["check", "--sorry", "M.B"])

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.B.middle") == "M.B.middle SKIP"
        assert "taken as granted (--sorry)" in result.output
        assert check_calls(fake_axle) == []
        assert "Checked 1 selection(s): all OK, 1 skipped" in result.output

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

    def test_sorry_on_own_module_judges_the_rest(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """`--select M --sorry M.A`: the module is judged with A's
        declarations stubbed (a partial grant inside the selection)."""
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(main, ["check", "--select", "M", "--sorry", "M.A"])

        assert result.exit_code == 0, result.output
        content = check_calls(fake_axle)[0]["content"]
        assert "def base : Nat := sorry" in content
        assert "theorem top : middle = 2 := by decide" in content  # the rest judged
        assert "siblings stubbed: 2 declarations" in result.output

    def test_sorry_warnings_collapse_into_one_line(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """The stubs' own sorry-warnings are report noise: collapsed
        into one line; warnings from outside the stubbed subtree stay."""
        root = self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)
        fake_axle.check_result = make_response(
            CheckResponse,
            okay=True,
            lean_messages=Messages(
                [],
                [
                    "-:1:1-1:20: warning: declaration uses `sorry`",
                    "-:2:1-2:20: warning: declaration uses `sorry`",
                    "-:4:1: warning: something real",
                ],
                [],
            ),
        )

        result = runner.invoke(
            main, ["check", "--select", "M.C", "--sorry", "M.A"]
        )

        assert result.exit_code == 0, result.output
        assert "upstream stubbed: 2 declarations" in result.output
        # The real warning is kept, attributed to its file.
        assert "    M/B.lean:2:1: warning: something real" in result.output
        assert "declaration uses" not in result.output

    def test_stale_manifest_warns_with_the_compile_prescription(        self, make_project, tmp_path: Path, monkeypatch, fake_axle
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


class TestShare:
    """`--share` mints one share link per submission, on stdout only."""

    def test_share_prints_a_link_per_submission(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check", "--select", "M.A", "--share"])

        assert result.exit_code == 0, result.output
        assert (
            result.output.count("share: https://axle.test/check#r=fake-req-") == 1
        )
        assert "Share link(s) minted: 1" in result.output

        # Without the flag: no share lines at all.
        plain = runner.invoke(main, ["check", "--select", "M.A"])
        assert "share:" not in plain.output

    def test_share_failed_check_still_mints(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A failed check is exactly what you want to share."""
        root = make_project(tmp_path, NO_TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.check_result = make_response(CheckResponse, okay=False)

        result = runner.invoke(main, ["check", "--select", "M.A", "--share"])

        assert result.exit_code == 1
        assert "share: https://axle.test/check#r=fake-req-" in result.output
        assert "Share link(s) minted: 1" in result.output

    def test_share_mint_retries_a_transient_not_found(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Streaming mints fire right when the run completes.

        The share service may not have the run persisted in that
        instant and answers "request not found" — the mint retries
        instead of giving up immediately, and links once the run
        shows up.
        """
        root = make_project(tmp_path, NO_TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.share_status = [404, 201]

        result = runner.invoke(main, ["check", "--select", "M.A", "--share"])

        assert result.exit_code == 0, result.output
        assert len(fake_axle.share_requests) == 2  # first attempt, retry
        assert "share: https://axle.test/check#r=fake-req-" in result.output
        assert "Share link(s) minted: 1" in result.output

    def test_share_failure_warns_but_leaves_the_exit_code(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.share_status = 404

        result = runner.invoke(main, ["check", "--select", "M.A", "--share"])

        assert result.exit_code == 0, result.output
        assert "share: unavailable (" in result.output
        assert "Share link(s) minted" not in result.output

    def test_share_network_failure_warns_too(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        import aiohttp

        root = make_project(tmp_path, NO_TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.share_status = aiohttp.ClientConnectionError("connection refused")

        result = runner.invoke(main, ["check", "--select", "M.A", "--share"])

        assert result.exit_code == 0, result.output
        assert "share: unavailable (" in result.output

    def test_share_skipped_selections_get_no_link(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(
            main, ["check", "--select", "M.A", "--sorry", "M.A", "--share"]
        )

        assert result.exit_code == 0, result.output
        assert "SKIP" in result.output
        assert "share:" not in result.output

    def test_share_records_nothing_extra_in_the_manifest(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """--share itself persists nothing: a shared run's manifest is
        identical to a plain run's. (An okay check does record its
        per-declaration check stamps — the point here is that sharing
        adds nothing beyond that.)"""
        import datetime as dt_module
        import json

        class _FixedDatetime(dt_module.datetime):
            """A clock stamping identical `checked_at` in both runs."""

            @classmethod
            def now(cls, tz=None):  # noqa: ARG002 - the interface is positional
                return dt_module.datetime(2026, 1, 1, tzinfo=dt_module.timezone.utc)

        monkeypatch.setattr("axle_build_tool.cli.datetime", _FixedDatetime)

        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        roots = {}
        for name in ("plain", "shared"):
            root = make_project(tmp_path / name, NO_TARGETS_CONFIG, TWO_FILES)
            monkeypatch.chdir(root)
            fake_axle._request_counter = 0  # identical request ids in both fixtures
            assert runner.invoke(main, ["compile"]).exit_code == 0
            roots[name] = root

        monkeypatch.chdir(roots["shared"])
        fake_axle._request_counter = 0  # ...and for the checks: same ids here too
        shared = runner.invoke(main, ["check", "--no-compile", "--select", "M.A", "--share"])
        assert shared.exit_code == 0, shared.output
        assert "share: https://axle.test/check#r=fake-req-" in shared.output

        monkeypatch.chdir(roots["plain"])
        fake_axle._request_counter = 0  # ...and for the plain run
        plain = runner.invoke(main, ["check", "--no-compile", "--select", "M.A"])
        assert plain.exit_code == 0, plain.output

        def manifest_of(name: str) -> dict:
            return json.loads(manifest_path(roots[name]).read_text(encoding="utf-8"))

        plain_manifest = manifest_of("plain")
        shared_manifest = manifest_of("shared")
        # The compile-time clocks differ between the fixtures; the
        # outcome data (including the fixed `checked_at`) must not.
        shared_manifest["generated_at"] = plain_manifest["generated_at"]
        for shared_node, plain_node in zip(
            shared_manifest["nodes"], plain_manifest["nodes"]
        ):
            shared_node["last_checked"] = plain_node["last_checked"]
        assert shared_manifest == plain_manifest


class TestStreaming:
    def test_results_print_in_completion_order_with_timing(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Each result prints as its submission completes, with timing.

        B's submission finishes first, so its report line prints before
        A's — completion order, not selection order — and every result
        line carries its progress counter and elapsed time, with the
        total in the summary.
        """
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["check"]).exit_code == 0
        # A's own-file marker routes the delay to A only; the marker
        # routing picks the one occurring latest in a payload, and B's
        # payload (dependencies inlined) ends with `def t2 := t1`.
        fake_axle.check_delays = {"def t1 := 1": 0.15, "def t2 := t1": 0.0}

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 0, result.output
        streamed = [
            line
            for line in result.output.splitlines()
            if re.match(r"\[\s*\d+/\d+\] ", line)
        ]
        # B completes first and streams first, each line numbered and timed.
        assert ["M.B.t2", "M.A.t1"] == [line.split()[1] for line in streamed]
        for position, line in enumerate(streamed, 1):
            assert re.match(rf"\[\s*{position}/2\] ", line), line
            assert re.search(r"\d+\.\d{3}s$", line), line
        def _delay(line: str) -> float:
            return float(line.split()[-1].removesuffix("s"))
        # A carried the artificial delay; the timing is per item, not
        # the whole run.
        assert _delay(streamed[1]) > _delay(streamed[0])
        assert re.search(r"Checked 2 selection\(s\): all OK in \d+\.\d{3}s", result.output)


class TestFailFast:
    """--fail-fast (-x): the first failed selection cancels the rest."""

    TARGETS_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets:
      - A.t1
      - B.t2
      - C.t3
"""

    FILES = {
        "M/A.lean": "def t1 := 1\n",
        "M/B.lean": "import A\ndef t2 := t1\n",
        "M/C.lean": "import A\nimport B\ndef t3 := t2\n",
    }

    DOCS = {
        "def t1 := 1": {
            "t1": make_document(
                "t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1"
            )
        },
        "def t2 := t1": {
            "t2": make_document(
                "t2", kind="def", line_pos=3, end_line_pos=3, signature="def t2"
            )
        },
        "def t3 := t2": {
            "t3": make_document(
                "t3", kind="def", line_pos=5, end_line_pos=5, signature="def t3"
            )
        },
    }

    def test_first_failure_cancels_in_flight_submissions(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """The failing result streams first and cuts the run short.

        The first failure is reported with its timing and message
        block; submissions still in flight are cancelled rather than
        finished, and the summary accounts for what was not judged.
        """
        root = make_project(tmp_path, self.TARGETS_CONFIG, self.FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        fake_axle.request_ids.clear()
        fake_axle.check_result = make_response(CheckResponse, okay=False)
        fake_axle.check_delays = {"def t2 := t1": 0.5, "def t3 := t2": 0.5}

        result = runner.invoke(main, ["check", "-x"])

        assert result.exit_code == 1, result.output
        # The delayed submissions were cancelled in flight: they never
        # came back from the API (request ids mint on response only).
        assert len(fake_axle.request_ids) == 1
        streamed = [
            line
            for line in result.output.splitlines()
            if re.match(r"\[\s*\d+/\d+\] ", line)
        ]
        assert len(streamed) == 1
        assert "M.A.t1" in streamed[0]
        assert "FAIL" in streamed[0]
        assert "fail-fast: cancelled 2 remaining selection(s)" in result.output
        assert re.search(
            r"Checked 3 selection\(s\): 1 failed, 0 OK, "
            r"2 cancelled by fail-fast in \d+\.\d{3}s",
            result.output,
        )

    def test_fail_fast_leaves_happy_runs_untouched(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, TWO_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TWO_FILE_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["check", "--fail-fast"])

        assert result.exit_code == 0, result.output
        assert "Checked 2 selection(s): all OK" in result.output


class TestCheckStamps:
    """Clean check outcomes are recorded per declaration in the manifest.

    Check and verify are distinct verdict tiers, so check carries its
    own stamp set (`checked_sig`/`checked_at`/`checked_request_id`),
    keyed on the same closure signature material as the verify cache
    and only written for full, unstubbed payloads that actually passed.
    """

    FILES = {
        "M/A.lean": "def t1 := 1\n",
        "M/B.lean": "import A\ndef t2 := t1\n",
    }
    DOCS = TWO_FILE_DOCS

    def compile_project(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> Path:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, self.FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        return root

    def expected_sig(self, root: Path, node_name: str) -> str:
        """The closure signature a stamped declaration should carry."""
        from axle_build_tool.manifest import closure_signature

        return closure_signature(
            load_manifest(root).by_name()[node_name],
            load_manifest(root),
            "lean-4.35.0",
            load_config(root).axle.global_options,
        )

    def test_file_selection_stamps_its_own_declarations_only(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A file-level selection stamps every declaration of the file —
        and nothing beyond it: closure dependencies are not stamped
        (their own hosts stamp them when judged)."""
        root = self.compile_project(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(main, ["check", "--select", "M.B"])

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"
        t2 = checked_stamp_of(load_manifest(root), "t2")
        t1 = checked_stamp_of(load_manifest(root), "t1")
        assert t2.checked_sig == self.expected_sig(root, "M.B")
        assert t2.checked_at is not None
        assert t2.checked_request_id in fake_axle.request_ids
        # The inlined dependency stays unstamped.
        assert t1.checked_sig is None
        assert t1.checked_at is None
        assert "Recorded 1 check stamp(s) in the manifest" in result.output

    def test_declaration_selection_stamps_its_one_declaration(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = self.compile_project(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(main, ["check", "--select", "M.B.t2"])

        assert result.exit_code == 0, result.output
        t2 = checked_stamp_of(load_manifest(root), "t2")
        assert t2.checked_sig == self.expected_sig(root, "M.B")
        assert t2.checked_request_id in fake_axle.request_ids
        assert checked_stamp_of(load_manifest(root), "t1").checked_sig is None

    def test_module_selection_stamps_every_declaration_of_its_nodes(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = self.compile_project(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(main, ["check", "--select", "M"])

        assert result.exit_code == 0, result.output
        manifest = load_manifest(root)
        for name, node_name in (("t1", "M.A"), ("t2", "M.B")):
            decl = checked_stamp_of(manifest, name)
            assert decl.checked_sig == self.expected_sig(root, node_name)
            assert decl.checked_request_id in fake_axle.request_ids

    def test_failing_payload_stamps_nothing(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Only successes are stamped — a failing payload leaves every
        judged declaration unstamped (the report's per-decl OK
        fallbacks stay report-only judgments)."""
        root = self.compile_project(make_project, tmp_path, monkeypatch, fake_axle)
        fake_axle.check_result = make_response(CheckResponse, okay=False)

        result = runner.invoke(main, ["check", "--select", "M"])

        assert result.exit_code == 1
        manifest = load_manifest(root)
        for decl in (d for node in manifest.nodes for d in node.declarations):
            assert decl.checked_sig is None
            assert decl.checked_at is None
            assert decl.checked_request_id is None

    def test_sorry_granted_run_stamps_nothing_even_when_okay(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A check against a `--sorry`-stubbed payload is not the
        full-context fact the signature claims — nothing is stamped,
        including the selection's own declarations."""
        chain = TestSorry()
        root = chain.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(main, ["check", "--select", "M.C", "--sorry", "M.A"])

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.C.top") == "M.C.top OK"
        manifest = load_manifest(root)
        for name in ("base", "base_holds", "middle", "top"):
            decl = checked_stamp_of(manifest, name)
            assert decl.checked_sig is None
            assert decl.checked_at is None

    def test_partially_granted_module_stamps_nothing(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """`--select M --sorry M.A`: B and C pass against a stubbed
        dependency — the payload is not the full closure, so no
        declaration in it is stamped."""
        chain = TestSorry()
        root = chain.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(main, ["check", "--select", "M", "--sorry", "M.A"])

        assert result.exit_code == 0, result.output
        manifest = load_manifest(root)
        for name in ("base", "base_holds", "middle", "top"):
            assert checked_stamp_of(manifest, name).checked_sig is None

    def test_fully_granted_selection_is_skipped_and_stamps_nothing(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = self.compile_project(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(main, ["check", "--select", "M.A", "--sorry", "M.A"])

        assert result.exit_code == 0, result.output
        assert status_line(result.output, "M.A") == "M.A SKIP"
        assert checked_stamp_of(load_manifest(root), "t1").checked_sig is None
        assert checked_stamp_of(load_manifest(root), "t2").checked_sig is None

    def test_environment_change_invalidates_the_stamp_key(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """`checked_sig` folds the environment in: same sources under
        another environment stamp a different signature, so a future
        check cache (and any consumer of the stamps) can tell them apart."""
        root = self.compile_project(make_project, tmp_path, monkeypatch, fake_axle)
        assert runner.invoke(
            main, ["check", "--select", "M.A", "--no-compile"]
        ).exit_code == 0
        first = checked_stamp_of(load_manifest(root), "t1").checked_sig

        (root / "axbt_project.yml").write_text(
            pinned_config("lean-4.35.0").replace("lean-4.35.0", "lean-4.34.1"),
            encoding="utf-8",
        )
        fake_axle._environments = [{"name": "lean-4.35.0"}, {"name": "lean-4.34.1"}]
        assert runner.invoke(
            main, ["check", "--select", "M.A", "--no-compile"]
        ).exit_code == 0

        second = checked_stamp_of(load_manifest(root), "t1").checked_sig
        assert second is not None and second != first

    def test_stamped_report_keeps_counters_and_timing_unchanged(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Stamping rides the completion loop: the streamed report's
        counters, orderings, and per-item timings are exactly as before."""
        root = make_project(tmp_path, TARGETS_CONFIG, self.FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        # A's own-file marker routes the delay to A only; the marker
        # routing picks the one occurring latest in a payload, and B's
        # payload (dependencies inlined) ends with `def t2 := t1`.
        fake_axle.check_delays = {"def t1 := 1": 0.15, "def t2 := t1": 0.0}

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 0, result.output
        streamed = [
            line
            for line in result.output.splitlines()
            if re.match(r"\[\s*\d+/\d+\] ", line)
        ]
        assert ["M.B.t2", "M.A.t1"] == [line.split()[1] for line in streamed]
        for position, line in enumerate(streamed, 1):
            assert re.match(rf"\[\s*{position}/2\] ", line), line
            assert re.search(r"\d+\.\d{3}s$", line), line
        assert re.search(r"Checked 2 selection\(s\): all OK in \d+\.\d{3}s", result.output)
        # Both targets stamped their own decl.
        manifest = load_manifest(root)
        assert checked_stamp_of(manifest, "t1").checked_sig is not None
        assert checked_stamp_of(manifest, "t2").checked_sig is not None
