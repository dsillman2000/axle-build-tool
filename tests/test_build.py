"""CLI-level tests for `axbt build`: check then verify in one run.

`build` orchestrates the two tier commands in sequence — the check
tier streams first, then the verify tier over the same selections,
skipping those whose check failed. In build mode every verdict row
carries a `[check]`/`[verify]` tier suffix, and the run exits nonzero
if either tier failed.
"""

from __future__ import annotations

from pathlib import Path

from click.testing import CliRunner

from axle_build_tool import main
from conftest import make_document, status_line

runner = CliRunner()

#: Two independent selections whose payloads share no content, so
#: per-marker routing can fail a check in one without the other.
BUILD_FILES = {
    "M/A.lean": "theorem t1 : 1 = 1 := rfl\n",
    "M/B.lean": "theorem t2 : 2 = 2 := rfl\n",
}

BUILD_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets:
      - A.t1
      - B.t2
"""

BUILD_DOCS = {
    "theorem t1 : 1 = 1 := rfl": {
        "t1": make_document(
            "t1", kind="theorem", line_pos=1, end_line_pos=1, signature="theorem t1"
        )
    },
    "theorem t2 : 2 = 2 := rfl": {
        "t2": make_document(
            "t2", kind="theorem", line_pos=1, end_line_pos=1, signature="theorem t2"
        )
    },
}


def check_calls(fake_axle) -> list[dict]:
    return [kwargs for method, kwargs in fake_axle.calls if method == "check"]


def verify_calls(fake_axle) -> list[dict]:
    return [kwargs for method, kwargs in fake_axle.calls if method == "verify_proof"]


def tagged_rows(output: str, tier: str) -> list[str]:
    """The verdict rows tagged with `tier`."""
    return [
        line
        for line in output.splitlines()
        if line.rstrip().endswith(f"[{tier}]")
    ]


class TestBuildSequencing:
    def test_build_runs_check_then_verify_over_both_selections(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, BUILD_CONFIG, BUILD_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = BUILD_DOCS

        result = runner.invoke(main, ["build"])

        assert result.exit_code == 0, result.output
        output = result.output
        # Both tiers submitted both selections.
        assert len(check_calls(fake_axle)) == 2
        assert len(verify_calls(fake_axle)) == 2
        assert "Checked 2 selection(s): all OK" in output
        assert "Verified 2 selection(s): all OK" in output
        assert "Built 2 selection(s): all OK in" in output
        # The check pass streams before the verify pass.
        check_rows = tagged_rows(output, "check")
        verify_rows = tagged_rows(output, "verify")
        assert len(check_rows) == len(verify_rows) == 2
        assert output.index(check_rows[0]) < output.index(verify_rows[0])
        assert output.index(check_rows[-1]) < output.index(verify_rows[0])
        # Both verdicts of a selection share the label+status shape the
        # single-tier reports produce (the tag is suffix-only).
        assert status_line(output, "M.A.t1") == "M.A.t1 OK"
        assert status_line(output, "M.B.t2") == "M.B.t2 OK"

    def test_the_verify_pass_presents_each_selection_on_request(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Same selection grammar: a --select build runs exactly one
        selection through both passes."""
        root = make_project(tmp_path, BUILD_CONFIG, BUILD_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = BUILD_DOCS

        result = runner.invoke(main, ["build", "--select", "M.A.t1"])

        assert result.exit_code == 0, result.output
        assert len(check_calls(fake_axle)) == 1
        assert len(verify_calls(fake_axle)) == 1
        assert "Built 1 selection(s): all OK in" in result.output
        assert result.output.count("[check]") == 1
        assert result.output.count("[verify]") == 1

    def test_a_failed_check_skips_verifying_that_selection(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, BUILD_CONFIG, BUILD_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = BUILD_DOCS
        #: Route the failure to t2's payload only (the two selections'
        #: payloads share no content).
        fake_axle.check_failures.add("theorem t2 : 2 = 2")

        result = runner.invoke(main, ["build"])

        assert result.exit_code == 1, result.output
        assert status_line(result.output, "M.B.t2") == "M.B.t2 FAIL"
        # The check pass failed t2; the verify pass skipped it without a
        # submission and verified t1.
        contents = [call.get("content", "") for call in verify_calls(fake_axle)]
        assert len(contents) == 1
        assert "theorem t1 : 1 = 1 := rfl" in contents[0]
        assert "check pass failed this selection above" in result.output
        assert any(
            "SKIP" in line for line in tagged_rows(result.output, "verify")
        )
        assert "Built 2 selection(s): 1 failed, 1 OK in" in result.output

    def test_fail_fast_in_the_check_pass_abandons_the_build(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, BUILD_CONFIG, BUILD_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = BUILD_DOCS
        fake_axle.check_failures.add("theorem t2 : 2 = 2")
        fake_axle.max_concurrency = 1

        result = runner.invoke(main, ["build", "--fail-fast"])

        assert result.exit_code == 1, result.output
        # The check pass stopped early; the build did not verify at all.
        assert tagged_rows(result.output, "verify") == []
        assert verify_calls(fake_axle) == []
        assert "Build stopped by fail-fast in the check pass; verify not run" in (
            result.output
        )
