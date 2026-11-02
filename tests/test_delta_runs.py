"""Tests for issue #28: files as units + content-addressed delta runs."""

from pathlib import Path

import pytest
from click.testing import CliRunner

from axle_build_tool import main
from conftest import make_document

runner = CliRunner()

CONFIG = """\
project:
  name: proj
modules:
  M: {}
"""

FILES = {"M/A.lean": "def t1 := 1\n", "M/B.lean": "import A\ndef t2 := t1\n"}

DOCS = {
    "def t1 := 1": {"t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")},
    "def t2 := t1": {"t2": make_document("t2", kind="def", line_pos=3, end_line_pos=3, signature="def t2")},
}


def test_check_second_run_is_cached(make_project, tmp_path, monkeypatch, fake_axle):
    root = make_project(tmp_path, CONFIG, FILES)
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = DOCS
    assert runner.invoke(main, ["compile"]).exit_code == 0
    fake_axle.calls.clear()

    first = runner.invoke(main, ["check"])
    assert first.exit_code == 0, first.output
    assert "Recorded 2 check stamp(s)" in first.output

    fake_axle.calls.clear()
    second = runner.invoke(main, ["check"])
    assert second.exit_code == 0, second.output
    assert "OK (cached)" in second.output
    methods = [m for m, _ in fake_axle.calls]
    assert "check" not in methods


def test_check_force_rejudges(make_project, tmp_path, monkeypatch, fake_axle):
    root = make_project(tmp_path, CONFIG, FILES)
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = DOCS
    assert runner.invoke(main, ["compile"]).exit_code == 0

    runner.invoke(main, ["check"])
    fake_axle.calls.clear()

    forced = runner.invoke(main, ["check", "--force"])
    assert forced.exit_code == 0, forced.output
    methods = [m for m, _ in fake_axle.calls]
    assert methods.count("check") == 2


def test_deprecation_warning_for_targets(make_project, tmp_path, monkeypatch, fake_axle):
    config = """\
project:
  name: proj
modules:
  M:
    targets:
      - A.t1
"""
    root = make_project(tmp_path, config, {"M/A.lean": "def t1 := 1\n"})
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = {
        "def t1 := 1": {"t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")}
    }
    assert runner.invoke(main, ["compile"]).exit_code == 0
    result = runner.invoke(main, ["check"])
    assert "deprecated" in result.output


def test_build_prints_compiled_once(make_project, tmp_path, monkeypatch, fake_axle):
    root = make_project(tmp_path, CONFIG, FILES)
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = DOCS
    assert runner.invoke(main, ["compile"]).exit_code == 0
    fake_axle.calls.clear()

    result = runner.invoke(main, ["build"])
    assert result.exit_code == 0, result.output
    # The Compiled/Wrote block should appear once (precursor short-circuit).
    assert result.output.count("Compiled 2 file(s)") == 1


def test_project_flag_runs_from_other_cwd(make_project, tmp_path, monkeypatch, fake_axle):
    root = make_project(tmp_path, "project:\n  name: proj\nmodules:\n  M: {}\n", {"M/A.lean": "def t1 := 1\n"})
    monkeypatch.chdir(tmp_path)
    fake_axle._extract_documents_by_marker = {
        "def t1 := 1": {"t1": __import__("conftest").make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")}
    }
    result = runner.invoke(main, ["--project", str(root), "compile"])
    assert result.exit_code == 0, result.output
    result = runner.invoke(main, ["--project", str(root), "check"])
    assert result.exit_code == 0, result.output


def test_project_env_var(make_project, tmp_path, monkeypatch, fake_axle):
    root = make_project(tmp_path, "project:\n  name: proj\nmodules:\n  M: {}\n", {"M/A.lean": "def t1 := 1\n"})
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("AXBT_PROJECT_DIR", str(root))
    fake_axle._extract_documents_by_marker = {
        "def t1 := 1": {"t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")}
    }
    result = runner.invoke(main, ["compile"])
    assert result.exit_code == 0, result.output


def test_short_select_alias(make_project, tmp_path, monkeypatch, fake_axle):
    root = make_project(tmp_path, "project:\n  name: proj\nmodules:\n  M: {}\n", {"M/A.lean": "def t1 := 1\n", "M/B.lean": "def t2 := 2\n"})
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = {
        "def t1 := 1": {"t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")},
        "def t2 := 2": {"t2": make_document("t2", kind="def", line_pos=1, end_line_pos=1, signature="def t2")},
    }
    assert runner.invoke(main, ["compile"]).exit_code == 0
    fake_axle.calls.clear()
    result = runner.invoke(main, ["check", "-s", "M.A"])
    assert result.exit_code == 0, result.output
    assert sum(1 for m,_ in fake_axle.calls if m=="check")==1


def test_select_space_union(make_project, tmp_path, monkeypatch, fake_axle):
    root = make_project(tmp_path, "project:\n  name: proj\nmodules:\n  M: {}\n", {"M/A.lean": "def t1 := 1\n", "M/B.lean": "def t2 := 2\n"})
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = {
        "def t1 := 1": {"t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")},
        "def t2 := 2": {"t2": make_document("t2", kind="def", line_pos=1, end_line_pos=1, signature="def t2")},
    }
    assert runner.invoke(main, ["compile"]).exit_code == 0
    fake_axle.calls.clear()
    result = runner.invoke(main, ["check", "-s", "M.A M.B"])
    assert result.exit_code == 0, result.output
    assert sum(1 for m,_ in fake_axle.calls if m=="check")==2


def test_sorry_short_alias_and_union(make_project, tmp_path, monkeypatch, fake_axle):
    root = make_project(tmp_path, "project:\n  name: proj\nmodules:\n  M: {}\n", {"M/A.lean": "def t1 := 1\n", "M/B.lean": "import A\ndef t2 := t1\n"})
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = {
        "def t1 := 1": {"t1": make_document("t1", kind="def", line_pos=1, end_line_pos=1, signature="def t1")},
        "def t2 := t1": {"t2": make_document("t2", kind="def", line_pos=3, end_line_pos=3, signature="def t2")},
    }
    assert runner.invoke(main, ["compile"]).exit_code == 0
    fake_axle.calls.clear()
    result = runner.invoke(main, ["check", "-s", "M.B", "-z", "M.A"])
    assert result.exit_code == 0, result.output
