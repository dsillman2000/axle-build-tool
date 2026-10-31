"""CLI-level tests for `axbt list`, driven through the real entry point."""

from __future__ import annotations

from pathlib import Path

import pytest
from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.manifest import MANIFEST_VERSION, manifest_path
from conftest import make_document, normalized_lines

runner = CliRunner()

SIMPLE_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""

# A synthetic dependency-chain project: A carries a hoisted external
# import and a module docstring (so positions only line up if the
# keyword-snap + line-map attribution work), B imports A, C imports B
# and carries a sorried declaration.
LIST_FILES = {
    "M/A.lean": (
        "import Mathlib\n\n/-! Base. -/\n\ndef base := 1\n"
        "theorem base_thm : base = 1 := rfl\n"
    ),
    "M/B.lean": "import A\ntheorem middle_thm : base = 1 := rfl\n",
    "M/C.lean": "import B\ntheorem gap : 1 = 2 := by sorry\n",
}

# One-based payload coordinates for each file's own extraction call:
# A's section starts at payload line 3 (hoisted import + blank), B's at
# 9 (A's five kept lines, the blank separator, then B), C's at 11.
LIST_DOCS = {
    "def base := 1": {
        "base": make_document("base", kind="def", line_pos=6, end_line_pos=6),
        "base_thm": make_document(
            "base_thm", kind="theorem", line_pos=7, end_line_pos=7
        ),
    },
    "theorem middle_thm": {
        "middle_thm": make_document(
            "middle_thm", kind="theorem", line_pos=9, end_line_pos=9
        )
    },
    "theorem gap": {
        "gap": make_document("gap", kind="theorem", line_pos=11, end_line_pos=11, is_sorry=True)
    },
}


@pytest.fixture
def compiled_project(tmp_path, make_project, fake_axle, monkeypatch) -> Path:
    """The synthetic chain project, compiled against the fake Axle client."""
    fake_axle._extract_documents_by_marker = LIST_DOCS
    root = make_project(tmp_path, SIMPLE_CONFIG, LIST_FILES)
    monkeypatch.chdir(root)
    result = runner.invoke(main, ["compile"])
    assert result.exit_code == 0, result.output
    return root


class TestHelp:
    def test_help_lists_init_compile_check_verify_and_list(self) -> None:
        result = runner.invoke(main, ["--help"])
        assert result.exit_code == 0
        for command in ("init", "compile", "check", "verify", "debug", "list"):
            assert command in result.output


class TestList:
    def test_list_prints_declaration_tree_in_topological_order(
        self, compiled_project: Path
    ) -> None:
        result = runner.invoke(main, ["list"])

        assert result.exit_code == 0, result.output
        file_lines = [
            line
            for line in result.output.splitlines()
            if line and not line.startswith("    ")
        ]
        assert [line.split(" ", 1)[0] for line in file_lines] == ["M.A", "M.B", "M.C"]
        lines = normalized_lines(result.output)
        assert "def base [line 5]" in lines
        assert "theorem base_thm [line 6]" in lines
        assert "theorem middle_thm [line 2]" in lines
        assert "theorem gap [line 2, sorry]" in lines
        # File paths are shown for inspection.
        assert "(M/A.lean)" in result.output

    def test_list_shows_sorry_marker(self, compiled_project: Path) -> None:
        result = runner.invoke(main, ["list"])

        assert result.exit_code == 0, result.output
        assert "theorem gap [line 2, sorry]" in normalized_lines(result.output)

    def test_list_without_manifest_fails_with_compile_hint(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, {"M/A.lean": "def x := 1\n"})
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["list"])

        assert result.exit_code != 0
        assert "compile" in result.output

    def test_list_with_stale_manifest_fails_with_compile_hint(
        self, compiled_project: Path
    ) -> None:
        import json

        raw = json.loads(manifest_path(compiled_project).read_text(encoding="utf-8"))
        raw["version"] = MANIFEST_VERSION + 1
        manifest_path(compiled_project).write_text(json.dumps(raw, indent=2), encoding="utf-8")

        result = runner.invoke(main, ["list"])

        assert result.exit_code != 0
        assert "compile" in result.output

    def test_list_outside_project_fails(self, tmp_path: Path, monkeypatch) -> None:
        monkeypatch.chdir(tmp_path)

        result = runner.invoke(main, ["list"])

        assert result.exit_code != 0
        assert "axbt_project.yml" in result.output


class TestListSelection:
    def test_module_selection_shows_every_file(self, compiled_project: Path) -> None:
        result = runner.invoke(main, ["list", "--select", "M"])

        assert result.exit_code == 0, result.output
        assert result.output.count("(") == 3  # three file headers
        assert "theorem middle_thm [line 2]" in normalized_lines(result.output)

    def test_file_selection_shows_one_file(self, compiled_project: Path) -> None:
        result = runner.invoke(main, ["list", "--select", "M.B"])

        assert result.exit_code == 0, result.output
        file_lines = [
            line
            for line in result.output.splitlines()
            if line and not line.startswith("    ")
        ]
        assert [line.split(" ", 1)[0] for line in file_lines] == ["M.B"]
        assert "theorem middle_thm [line 2]" in normalized_lines(result.output)
        assert "base_thm" not in result.output

    def test_declaration_selection_shows_one_declaration(
        self, compiled_project: Path
    ) -> None:
        result = runner.invoke(main, ["list", "--select", "M.A.base_thm"])

        assert result.exit_code == 0, result.output
        assert "M.A" in result.output
        assert "theorem base_thm [line 6]" in normalized_lines(result.output)
        assert "middle_thm" not in result.output

    def test_unknown_selection_fails_with_guidance(self, compiled_project: Path) -> None:
        result = runner.invoke(main, ["list", "--select", "Nope"])

        assert result.exit_code != 0
        assert "Unknown module 'Nope'" in result.output
        assert "M" in result.output  # valid modules listed
