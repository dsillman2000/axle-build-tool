"""CLI-level tests for `axbt list`, driven through the real entry point."""

from __future__ import annotations

from pathlib import Path

import pytest
from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.manifest import MANIFEST_VERSION, manifest_path
from conftest import normalized_lines

runner = CliRunner()

SIMPLE_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""


def fresh_demo(demos_dir: Path, name: str) -> Path:
    demo = demos_dir / name
    import shutil

    shutil.rmtree(demo / ".axbt", ignore_errors=True)
    return demo


@pytest.fixture
def compiled_demo(demos_dir: Path, fake_axle, monkeypatch) -> Path:
    """The RootTwoIrrational demo, compiled against the fake Axle client."""
    from conftest import DEMO_EXTRACTION_DOCS, normalized_lines

    demo = fresh_demo(demos_dir, "RootTwoIrrational")
    fake_axle._extract_documents_by_marker = DEMO_EXTRACTION_DOCS
    monkeypatch.chdir(demo)
    result = runner.invoke(main, ["compile"])
    assert result.exit_code == 0, result.output
    return demo


class TestHelp:
    def test_help_lists_init_compile_check_verify_and_list(self) -> None:
        result = runner.invoke(main, ["--help"])
        assert result.exit_code == 0
        for command in ("init", "compile", "check", "verify", "list"):
            assert command in result.output


class TestList:
    def test_list_prints_declaration_tree_in_topological_order(
        self, compiled_demo: Path
    ) -> None:
        result = runner.invoke(main, ["list"])

        assert result.exit_code == 0, result.output
        file_lines = [
            line
            for line in result.output.splitlines()
            if line and not line.startswith("    ")
        ]
        assert [line.split(" ", 1)[0] for line in file_lines] == [
            "RootTwoIrrational.Divisibility",
            "RootTwoIrrational.EuclidLemma",
            "RootTwoIrrational.IrrationalSqrtTwo",
        ]
        assert "theorem prime_gt_one [line 11]" in normalized_lines(result.output)
        assert "theorem prime_dvd_square [line 15]" in normalized_lines(result.output)
        assert "theorem euclid_lemma [line 12]" in normalized_lines(result.output)
        assert "theorem sqrt_two_irrational [line 15]" in normalized_lines(result.output)
        # File paths are shown for inspection.
        assert "(RootTwoIrrational/Divisibility.lean)" in result.output

    def test_list_shows_sorry_marker(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> None:
        from conftest import make_document

        fake_axle._extract_documents = {
            "open_problem": make_document("open_problem", is_sorry=True, line_pos=1, end_line_pos=1)
        }
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {"M/A.lean": "theorem open_problem : P := by sorry\n"},
        )
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["list"])

        assert result.exit_code == 0, result.output
        assert "theorem open_problem [line 1, sorry]" in normalized_lines(result.output)

    def test_list_without_manifest_fails_with_compile_hint(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, {"M/A.lean": "def x := 1\n"})
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["list"])

        assert result.exit_code != 0
        assert "compile" in result.output

    def test_list_with_stale_manifest_fails_with_compile_hint(
        self, compiled_demo: Path
    ) -> None:
        import json

        raw = json.loads(manifest_path(compiled_demo).read_text(encoding="utf-8"))
        raw["version"] = MANIFEST_VERSION + 1
        manifest_path(compiled_demo).write_text(json.dumps(raw, indent=2), encoding="utf-8")

        result = runner.invoke(main, ["list"])

        assert result.exit_code != 0
        assert "compile" in result.output

    def test_list_outside_project_fails(self, tmp_path: Path, monkeypatch) -> None:
        monkeypatch.chdir(tmp_path)

        result = runner.invoke(main, ["list"])

        assert result.exit_code != 0
        assert "axbt_project.yml" in result.output


class TestListSelection:
    def test_module_selection_shows_every_file(self, compiled_demo: Path) -> None:
        result = runner.invoke(main, ["list", "--select", "RootTwoIrrational"])

        assert result.exit_code == 0, result.output
        assert result.output.count("(") == 3  # three file headers
        assert "theorem euclid_lemma [line 12]" in normalized_lines(result.output)

    def test_file_selection_shows_one_file(self, compiled_demo: Path) -> None:
        result = runner.invoke(main, ["list", "--select", "RootTwoIrrational.EuclidLemma"])

        assert result.exit_code == 0, result.output
        file_lines = [
            line
            for line in result.output.splitlines()
            if line and not line.startswith("    ")
        ]
        assert [line.split(" ", 1)[0] for line in file_lines] == [
            "RootTwoIrrational.EuclidLemma"
        ]
        assert "theorem euclid_lemma [line 12]" in normalized_lines(result.output)
        assert "prime_gt_one" not in result.output

    def test_declaration_selection_shows_one_declaration(
        self, compiled_demo: Path
    ) -> None:
        result = runner.invoke(
            main, ["list", "--select", "RootTwoIrrational.Divisibility.prime_dvd_square"]
        )

        assert result.exit_code == 0, result.output
        assert "RootTwoIrrational.Divisibility" in result.output
        assert "theorem prime_dvd_square [line 15]" in normalized_lines(result.output)
        assert "prime_gt_one" not in result.output

    def test_unknown_selection_fails_with_guidance(self, compiled_demo: Path) -> None:
        result = runner.invoke(main, ["list", "--select", "Nope"])

        assert result.exit_code != 0
        assert "Unknown module 'Nope'" in result.output
        assert "RootTwoIrrational" in result.output  # valid modules listed

    def test_gauss_demo_list_via_selection(self, demos_dir: Path, fake_axle, monkeypatch) -> None:
        from conftest import make_document

        demo = fresh_demo(demos_dir, "GaussIntSum")
        # gauss_sum_identity's keyword sits at file line 16; with the single
        # hoisted import that is zero-based payload line 16.
        fake_axle._extract_documents = {
            "gauss_sum_identity": make_document("gauss_sum_identity", line_pos=16, end_line_pos=18)
        }
        monkeypatch.chdir(demo)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["list", "--select", "GaussIntSum.GaussSum.gauss_sum_identity"])

        assert result.exit_code == 0, result.output
        assert "theorem gauss_sum_identity [line 16]" in normalized_lines(result.output)
        assert "GaussIntSum.GaussSum (GaussIntSum/GaussSum.lean)" in result.output
