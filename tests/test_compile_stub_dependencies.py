"""Tests that `axbt compile` stubs upstream proof bodies for new/changed deps (issue #51)."""

from __future__ import annotations

from pathlib import Path

from click.testing import CliRunner

from axle_build_tool import main
from conftest import make_document

runner = CliRunner()

CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""

FILES = {
    "M/A.lean": "theorem t1 : 1 = 1 := by\n  rfl\n",
    "M/B.lean": "import A\ntheorem t2 : 1 = 1 := rfl\n",
}

DOCS = {
    "theorem t1 : 1 = 1": {
        "t1": make_document(
            "t1",
            kind="theorem",
            line_pos=1,
            end_line_pos=2,
            signature="theorem t1 : 1 = 1",
        )
    },
    "theorem t2 : 1 = 1": {
        "t2": make_document(
            "t2",
            kind="theorem",
            line_pos=2,
            end_line_pos=2,
            signature="theorem t2 : 1 = 1",
        )
    },
}


def _extract_content_for(fake_axle, marker: str) -> str:
    matches = [
        kw["content"]
        for method, kw in fake_axle.calls
        if method == "extract_decls" and marker in kw["content"]
    ]
    assert len(matches) == 1, f"expected 1 extract_decls call for {marker!r}, got {len(matches)}"
    return matches[0]


def test_initial_compile_stubs_new_upstream_proof_bodies(
    make_project, tmp_path: Path, monkeypatch, fake_axle
) -> None:
    root = make_project(tmp_path, CONFIG, FILES)
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = DOCS
    # Delay M.A to ensure M.B genuinely waits on M.A's extraction.
    fake_axle.extract_delays = {"theorem t1 : 1 = 1": 0.05}

    result = runner.invoke(main, ["compile"])
    assert result.exit_code == 0, result.output

    b_content = _extract_content_for(fake_axle, "theorem t2 : 1 = 1")
    assert "theorem t1 : 1 = 1 := by sorry" in b_content
    assert "theorem t1 : 1 = 1 := by\n  rfl" not in b_content


def test_changed_upstream_and_downstream_stubs_upstream_proof_bodies(
    make_project, tmp_path: Path, monkeypatch, fake_axle
) -> None:
    root = make_project(tmp_path, CONFIG, FILES)
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = DOCS
    assert runner.invoke(main, ["compile"]).exit_code == 0

    (root / "M/A.lean").write_text(
        "theorem t1 : 1 = 1 := by\n  exact rfl\n", encoding="utf-8"
    )
    (root / "M/B.lean").write_text(
        "import A\ntheorem t2 : 1 = 1 := rfl\n-- touched\n", encoding="utf-8"
    )
    fake_axle.calls.clear()

    result = runner.invoke(main, ["compile"])
    assert result.exit_code == 0, result.output

    b_content = _extract_content_for(fake_axle, "theorem t2 : 1 = 1")
    assert "theorem t1 : 1 = 1 := by sorry" in b_content
    assert "exact rfl" not in b_content


def test_full_refresh_stubs_upstream_proof_bodies(
    make_project, tmp_path: Path, monkeypatch, fake_axle
) -> None:
    root = make_project(tmp_path, CONFIG, FILES)
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = DOCS
    assert runner.invoke(main, ["compile"]).exit_code == 0
    fake_axle.calls.clear()

    result = runner.invoke(main, ["compile", "--full-refresh"])
    assert result.exit_code == 0, result.output

    b_content = _extract_content_for(fake_axle, "theorem t2 : 1 = 1")
    assert "theorem t1 : 1 = 1 := by sorry" in b_content
    assert "theorem t1 : 1 = 1 := by\n  rfl" not in b_content
