"""Tests for caching declaration-free aggregate files in `axbt check` (issue #54)."""

from __future__ import annotations

from pathlib import Path

from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.manifest import load_manifest
from conftest import make_document, status_line

runner = CliRunner()

AGG_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""

AGG_FILES = {
    "M/A.lean": "theorem t1 : 1 = 1 := rfl\n",
    "M/Agg.lean": "import A\n-- import-only aggregator\n",
}

AGG_DOCS = {
    "theorem t1 : 1 = 1": {
        "t1": make_document("t1", kind="theorem", line_pos=1, end_line_pos=1)
    },
}


def _check_calls(fake_axle) -> list[dict]:
    return [kw for method, kw in fake_axle.calls if method == "check"]


def test_declaration_free_aggregate_file_is_cached_on_second_check(
    make_project, tmp_path: Path, monkeypatch, fake_axle
) -> None:
    root = make_project(tmp_path, AGG_CONFIG, AGG_FILES)
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = AGG_DOCS
    assert runner.invoke(main, ["compile"]).exit_code == 0
    fake_axle.calls.clear()

    first = runner.invoke(main, ["check"])
    assert first.exit_code == 0, first.output
    assert len(_check_calls(fake_axle)) == 2
    agg_node = load_manifest(root).by_name()["M.Agg"]
    assert agg_node.declarations == []
    assert agg_node.checked_sig is not None
    assert agg_node.checked_at is not None
    assert agg_node.checked_request_id is not None

    fake_axle.calls.clear()
    second = runner.invoke(main, ["check"])
    assert second.exit_code == 0, second.output
    assert _check_calls(fake_axle) == []
    assert status_line(second.output, "M.Agg") == "M.Agg OK (cached)"

    # `--force` bypasses the node-level cache.
    fake_axle.calls.clear()
    forced = runner.invoke(main, ["check", "-s", "M.Agg", "--force"])
    assert forced.exit_code == 0, forced.output
    assert len(_check_calls(fake_axle)) == 1


def test_editing_aggregate_or_parent_invalidates_check_cache(
    make_project, tmp_path: Path, monkeypatch, fake_axle
) -> None:
    root = make_project(tmp_path, AGG_CONFIG, AGG_FILES)
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = AGG_DOCS
    assert runner.invoke(main, ["compile"]).exit_code == 0
    assert runner.invoke(main, ["check"]).exit_code == 0

    # Editing parent M/A.lean invalidates M.Agg's closure signature.
    (root / "M/A.lean").write_text(
        "theorem t1 : 1 = 1 := rfl\n-- touched parent\n", encoding="utf-8"
    )
    fake_axle.calls.clear()
    after_parent = runner.invoke(main, ["check"])
    assert after_parent.exit_code == 0, after_parent.output
    assert len(_check_calls(fake_axle)) == 2

    # Editing M/Agg.lean itself invalidates M.Agg (while M.A stays cached).
    (root / "M/Agg.lean").write_text(
        "import A\n-- touched aggregate\n", encoding="utf-8"
    )
    fake_axle.calls.clear()
    after_agg = runner.invoke(main, ["check"])
    assert after_agg.exit_code == 0, after_agg.output
    assert len(_check_calls(fake_axle)) == 1
    assert status_line(after_agg.output, "M.A") == "M.A OK (cached)"


def test_cached_declaration_free_share_prints_recorded_request_id(
    make_project, tmp_path: Path, monkeypatch, fake_axle
) -> None:
    root = make_project(tmp_path, AGG_CONFIG, AGG_FILES)
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = AGG_DOCS
    assert runner.invoke(main, ["compile"]).exit_code == 0
    assert runner.invoke(main, ["check", "-s", "M.Agg"]).exit_code == 0
    rid = load_manifest(root).by_name()["M.Agg"].checked_request_id
    assert rid is not None

    fake_axle.calls.clear()
    cached = runner.invoke(main, ["check", "-s", "M.Agg", "--share"])
    assert cached.exit_code == 0, cached.output
    assert _check_calls(fake_axle) == []
    assert f"share: https://axle.test/check#r={rid}" in cached.output
    assert "(from the earlier run)" in cached.output
