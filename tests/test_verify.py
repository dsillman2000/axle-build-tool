"""CLI-level tests for `axbt verify`, driven through the real entry point."""

from __future__ import annotations

import re
import shutil
from pathlib import Path

import pytest

from axle.types import Messages, VerifyProofNegation, VerifyProofResponse
from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.manifest import load_manifest, save_manifest
from conftest import (
    _TIMESTAMP,
    make_document,
    make_response,
    raw_report_line,
    start_line,
    status_line,
    verified_stamp_of,
)

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

DEF_TARGETS_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets:
      - A.d1
      - B.d2
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


# Verify needs theorems: defs have no proof body and are skipped.
THEOREM_FILES = {
    "M/A.lean": "theorem t1 : 1 = 1 := rfl\n",
    "M/B.lean": "import A\ntheorem t2 : 1 = 1 := rfl\n",
}

# One-based payload coordinates: `t1` lives in A (payload line 1); `t2`
# in B, whose section starts at payload line 3 (A's single line is
# inlined first, then a blank separator).
THEOREM_DOCS = {
    "theorem t1 : 1 = 1": {
        "t1": make_document("t1", kind="theorem", line_pos=1, end_line_pos=1)
    },
    "theorem t2 : 1 = 1": {
        "t2": make_document("t2", kind="theorem", line_pos=3, end_line_pos=3)
    },
}

DEF_FILES = {"M/A.lean": "def d1 := 1\n", "M/B.lean": "import A\ndef d2 := d1\n"}
DEF_DOCS = {
    "def d1 := 1": {"d1": make_document("d1", kind="def", line_pos=1, end_line_pos=1)},
    "def d2 := d1": {"d2": make_document("d2", kind="def", line_pos=3, end_line_pos=3)},
}


def theorem2sorry_calls(fake_axle) -> list[dict]:
    return [kwargs for method, kwargs in fake_axle.calls if method == "theorem2sorry"]


def verify_calls(fake_axle) -> list[dict]:
    return [kwargs for method, kwargs in fake_axle.calls if method == "verify_proof"]


class TestTargetsDefault:
    def test_bare_verify_verifies_every_configured_target(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        # One theorem2sorry + one verify_proof per target.
        assert len(theorem2sorry_calls(fake_axle)) == 2
        assert len(verify_calls(fake_axle)) == 2
        # Submissions stream in completion order, so identify calls by
        # their formal statement rather than by log position.
        by_formal = {c["formal_statement"]: c for c in verify_calls(fake_axle)}
        first, second = by_formal["formal[t1]"], by_formal["formal[t2]"]
        # The formal statement is the theorem2sorry output; the content
        # is the standalone payload (dependencies inlined).
        assert first["formal_statement"] == "formal[t1]"
        assert "theorem t1 : 1 = 1 := rfl" in first["content"]
        assert second["formal_statement"] == "formal[t2]"
        assert "theorem t1 : 1 = 1 := rfl" in second["content"]
        assert "theorem t2 : 1 = 1 := rfl" in second["content"]
        # The API sweeps the whole content for incomplete proofs, so a
        # declaration-level verify excuses its payload's other theorems;
        # t1's payload has no other theorems, t2's has t1.
        assert first["permitted_sorries"] is None
        assert second["permitted_sorries"] == ["t1"]
        assert status_line(result.output, "M.A.t1") == "M.A.t1 OK"
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"
        assert "Verified 2 selection(s): all OK" in result.output

    def test_verify_uses_the_run_modes_of_check(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """--no-compile takes the manifest at face value; --full-refresh
        on a clean tree re-extracts everything first."""
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify", "--full-refresh"])

        assert result.exit_code == 0, result.output
        # Nothing changed, yet every file was re-extracted, then verified.
        assert len([m for m, _ in fake_axle.calls if m == "extract_decls"]) == 2
        assert len(verify_calls(fake_axle)) == 2

        fake_axle.calls.clear()
        result = runner.invoke(main, ["verify", "--no-compile"])

        assert result.exit_code == 0, result.output
        assert not [m for m, _ in fake_axle.calls if m == "extract_decls"]
        # The verifications from the first run are still cached (the
        # sources and config are unchanged): nothing is re-submitted.
        assert len(verify_calls(fake_axle)) == 0
        assert "(cached)" in result.output

    def test_full_refresh_conflicts_with_no_compile(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify", "--full-refresh", "--no-compile"])

        assert result.exit_code != 0
        assert "conflicts with --no-compile" in result.output


class TestSelection:
    def test_declaration_selection_focuses_the_named_theorem(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify", "--select", "M.B.t2"])

        assert result.exit_code == 0, result.output
        sorry_calls = theorem2sorry_calls(fake_axle)
        verify = verify_calls(fake_axle)
        assert len(sorry_calls) == 1 and len(verify) == 1
        assert sorry_calls[0]["names"] == ["t2"]
        assert verify[0]["formal_statement"] == "formal[t2]"
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"
        assert "Verified 1 selection(s): all OK" in result.output

    def test_module_selection_verifies_every_theorem_in_the_payload(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify", "--select", "M"])

        assert result.exit_code == 0, result.output
        sorry_calls = theorem2sorry_calls(fake_axle)
        assert len(sorry_calls) == 1
        # The formal statement covers exactly the to-verify theorems
        # (all of them on a first run) — file-level verify is strict
        # over the payload's every theorem.
        assert sorry_calls[0]["names"] == ["t1", "t2"]
        assert verify_calls(fake_axle)[0]["formal_statement"] == "formal[t1,t2]"
        assert verify_calls(fake_axle)[0]["permitted_sorries"] is None
        assert status_line(result.output, "M") == "M OK"


class TestSkipsAndLocalFailures:
    def test_definition_targets_are_skipped_with_a_note(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Defs have no proof body: nothing to verify, no API calls."""
        root = make_project(tmp_path, DEF_TARGETS_CONFIG, DEF_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = DEF_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        assert fake_axle.calls == [] or not [
            m for m, _ in fake_axle.calls if m in ("theorem2sorry", "verify_proof")
        ]
        assert status_line(result.output, "M.A.d1") == "M.A.d1 SKIP"
        assert "verify checks theorems/lemmas only" in result.output
        assert "Verified 2 selection(s): all OK, 2 skipped" in result.output

    def test_sorry_target_fails_locally_without_an_api_call(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        sorry_doc = {
            "theorem t1 : 1 = 1": {
                "t1": make_document(
                    "t1", kind="theorem", line_pos=1, end_line_pos=1, is_sorry=True
                )
            },
            "theorem t2 : 1 = 1": {
                "t2": make_document("t2", kind="theorem", line_pos=3, end_line_pos=3)
            },
        }
        fake_axle._extract_documents_by_marker = sorry_doc
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify", "--select", "M.A.t1"])

        assert result.exit_code == 1
        # Failed locally: not even the formal-statement roundtrip ran
        # (only the environment resolution upfront).
        assert not [m for m, _ in fake_axle.calls if m in ("theorem2sorry", "verify_proof")]
        assert status_line(result.output, "M.A.t1") == "M.A.t1 FAIL"
        assert "declaration 't1' has a `sorry`" in result.output

    def test_no_compile_without_manifest_fails_with_compile_hint(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["verify", "--no-compile"])

        assert result.exit_code != 0
        assert "compile" in result.output


class TestFailureReporting:
    def test_failure_prints_attributed_messages_and_exits_1(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        files = {"M/A.lean": "theorem t1 : 1 = 1 :=\n  rfl\n"}
        root = make_project(tmp_path, NO_TARGETS_CONFIG, files)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "theorem t1 : 1 = 1": {
                "t1": make_document("t1", kind="theorem", line_pos=1, end_line_pos=2)
            }
        }
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        # Payload line 2 (`  rfl`) is source line 2; positions are
        # attributed back through the payload's line map.
        fake_axle.verify_result = make_response(
            VerifyProofResponse,
            okay=False,
            negation=None,
            lean_messages=Messages(["-:2:3: error: boom"], [], []),
        )

        result = runner.invoke(main, ["verify", "--select", "M.A"])

        assert result.exit_code == 1
        assert status_line(result.output, "M.A") == "M.A FAIL"
        assert "    M/A.lean:2:3: error: boom" in result.output
        assert "Verified 1 selection(s): 1 failed, 0 OK" in result.output

    def test_failure_without_messages_reports_failed_declarations(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        fake_axle.verify_result = make_response(
            VerifyProofResponse,
            okay=False,
            negation=None,
            failed_declarations=["t1"],
        )

        result = runner.invoke(main, ["verify", "--select", "M.A"])

        assert result.exit_code == 1
        assert "failed declarations: t1" in result.output

    def test_provable_negation_fails_as_vacuous(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        fake_axle.verify_result = make_response(
            VerifyProofResponse,
            okay=True,
            negation=VerifyProofNegation(
                okay=True, tool_messages=Messages([], [], []), failed_declarations=[]
            ),
        )

        result = runner.invoke(main, ["verify", "--select", "M.A"])

        assert result.exit_code == 1
        assert status_line(result.output, "M.A") == "M.A FAIL"
        assert "the statement is vacuous" in result.output


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


class TestVerificationCache:
    """Successful verifications are recorded and skipped while valid."""

    def test_second_verify_skips_submissions(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        first = runner.invoke(main, ["verify"])
        assert first.exit_code == 0, first.output
        assert len(verify_calls(fake_axle)) == 2
        # The manifest records the verifications per declaration.
        manifest = load_manifest(root)
        stamps = [
            d.verified_sig
            for node in manifest.nodes
            for d in node.declarations
        ]
        assert all(sig is not None for sig in stamps)
        assert all(d.verified_at is not None for node in manifest.nodes for d in node.declarations)

        fake_axle.calls.clear()
        second = runner.invoke(main, ["verify"])

        assert second.exit_code == 0, second.output
        # Nothing re-submitted: every target is still validly cached.
        assert theorem2sorry_calls(fake_axle) == []
        assert verify_calls(fake_axle) == []
        assert second.output.count("(cached)") == 2
        assert "Verified 2 selection(s): all OK (2 cached)" in second.output

    def test_force_reverifies_and_restamps(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        assert runner.invoke(main, ["verify"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify", "--force"])

        assert result.exit_code == 0, result.output
        assert len(verify_calls(fake_axle)) == 2
        assert "(cached)" not in result.output

    def test_dependency_edit_invalidates_the_cache(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        assert runner.invoke(main, ["verify"]).exit_code == 0
        fake_axle.calls.clear()

        # A change anywhere in B's file (even a comment) changes B's md5
        # and therefore the closure signature of everything downstream.
        (root / "M/B.lean").write_text(
            "import A\ntheorem t2 : 1 = 1 := rfl\n-- touched\n", encoding="utf-8"
        )

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        # Both selections re-verify: B changed, and A's signature covers
        # its dependency closure (B is not A's dependency, so A's stamp
        # survives — but A.t1's selection re-verifies only if A changed;
        # here B.t2's selection must re-run).
        assert len(verify_calls(fake_axle)) == 1
        assert "(cached)" in result.output  # A.t1 stayed cached

    def test_environment_change_invalidates_the_cache(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, pinned_config("lean-4.35.0"), THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        assert runner.invoke(main, ["verify"]).exit_code == 0
        fake_axle.calls.clear()

        # Re-point the pin at another served environment: same sources,
        # different elaboration target — the cache must miss.
        (root / "axbt_project.yml").write_text(
            pinned_config("lean-4.34.1"), encoding="utf-8"
        )
        fake_axle._environments = [
            {"name": "lean-4.35.0"},
            {"name": "lean-4.34.1"},
        ]

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        # The same sources re-verify under the new environment: the
        # signature covers it, so the cache misses.
        assert len(verify_calls(fake_axle)) == 1
        assert verify_calls(fake_axle)[0]["environment"] == "lean-4.34.1"
        assert "(cached)" not in result.output


class TestBothStampTiers:
    """Check and verify are distinct verdicts, recorded independently.

    `checked_*` and `verified_*` live on the same declaration without
    interfering: the verify cache consults only `verified_sig` against
    the closure signature — check stamps never satisfy it, and stale
    check fields never disturb it.
    """

    def test_checked_and_verified_stamps_coexist(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        check_result = runner.invoke(main, ["check"])
        assert check_result.exit_code == 0, check_result.output
        checked_rids = {
            d.checked_request_id for n in load_manifest(root).nodes for d in n.declarations
        }
        fake_axle.calls.clear()

        verify_result = runner.invoke(main, ["verify"])
        assert verify_result.exit_code == 0, verify_result.output
        manifest = load_manifest(root)
        for name in ("t1", "t2"):
            decl = verified_stamp_of(manifest, name)
            assert decl.verified_sig is not None
            # Same closure signature material — the tiers differ in what
            # they judged, not in what content they judged against.
            assert decl.verified_sig == decl.checked_sig
            assert decl.checked_sig is not None
            assert decl.verified_request_id not in checked_rids

        # A second verify stays cached: the cache reads verified fields only.
        fake_axle.calls.clear()
        again = runner.invoke(main, ["verify", "--no-compile"])
        assert again.exit_code == 0, again.output
        assert again.output.count("(cached)") == 2
        assert verify_calls(fake_axle) == []

    def test_check_stamps_do_not_satisfy_the_verify_cache(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A declaration checked clean has not been kernel-verified;
        verify must still submit it."""
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        assert runner.invoke(main, ["check"]).exit_code == 0
        fake_axle.calls.clear()
        assert all(
            d.checked_sig is not None for n in load_manifest(root).nodes for d in n.declarations
        )

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        assert len(verify_calls(fake_axle)) == 2
        assert "(cached)" not in result.output

    def test_verify_cache_ignores_stale_check_fields(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        assert runner.invoke(main, ["verify"]).exit_code == 0

        # Corrupt every checked_* field after verifying: the cache must
        # keep working — verify's signature material excludes them.
        manifest = load_manifest(root)
        stamped_nodes = [
            node.model_copy(
                update={
                    "declarations": [
                        d.model_copy(
                            update={
                                "checked_sig": "bogus",
                                "checked_at": None,
                                "checked_request_id": "bogus",
                            }
                        )
                        for d in node.declarations
                    ]
                }
            )
            for node in manifest.nodes
        ]
        save_manifest(manifest.model_copy(update={"nodes": stamped_nodes}), root)
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify", "--no-compile"])

        assert result.exit_code == 0, result.output
        assert "(cached)" in result.output
        assert verify_calls(fake_axle) == []


class TestStartLines:
    """dbt-style START lines on verify too: one per actual submission,
    none for locally-answered selections (cached, skipped, sorried)."""

    def test_submitted_verifications_print_start_lines(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        # One START per submission, sharing the selection's counter with
        # its verdict, in place of a timing: `label START [RUN]`.
        assert start_line(result.output, "M.A.t1") == "M.A.t1 START [RUN]"
        assert start_line(result.output, "M.B.t2") == "M.B.t2 START [RUN]"
        for label in ("M.A.t1", "M.B.t2"):
            start_ts, start_counter = raw_report_line(result.output, label, "START")
            verdict_ts, verdict_counter = raw_report_line(result.output, label, "OK")
            assert start_counter == verdict_counter, label
            assert re.fullmatch(r"\d{2}:\d{2}:\d{2}\.\d{3}", start_ts), start_ts
        assert status_line(result.output, "M.A.t1") == "M.A.t1 OK"
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"

    def test_locally_answered_verifications_print_no_start(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """The second run is fully cached: verdicts print without any
        submission, therefore without any START line."""
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        assert runner.invoke(main, ["verify"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify", "--no-compile"])

        assert result.exit_code == 0, result.output
        assert result.output.count("(cached)") == 2
        assert "START" not in result.output

    def test_sorried_local_failure_prints_no_start(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        sorried_docs = {
            "theorem t1 : 1 = 1": {
                "t1": make_document(
                    "t1", kind="theorem", line_pos=1, end_line_pos=1, is_sorry=True
                )
            },
            "theorem t2 : 1 = 1": {
                "t2": make_document("t2", kind="theorem", line_pos=3, end_line_pos=3)
            },
        }
        fake_axle._extract_documents_by_marker = sorried_docs
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 1
        assert status_line(result.output, "M.A.t1") == "M.A.t1 FAIL"
        # t2 submitted (START + verdict); the locally-failed t1 did not.
        assert start_line(result.output, "M.B.t2") == "M.B.t2 START [RUN]"
        with pytest.raises(AssertionError):
            start_line(result.output, "M.A.t1")


class TestPermittedSorry:
    def test_permitted_sorries_excuse_the_guard_and_the_sweep(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A sorried declaration, explicitly excused, neither fails the
        run nor gets stamped as verified."""
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        sorried_docs = {
            "theorem t1 : 1 = 1": {
                "t1": make_document(
                    "t1", kind="theorem", line_pos=1, end_line_pos=1, is_sorry=True
                )
            },
            "theorem t2 : 1 = 1": {
                "t2": make_document("t2", kind="theorem", line_pos=3, end_line_pos=3)
            },
        }
        fake_axle._extract_documents_by_marker = sorried_docs
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(
            main, ["verify", "--permitted-sorries", "M.A.t1"]
        )

        assert result.exit_code == 0, result.output
        verify = verify_calls(fake_axle)[0]
        assert "t1" in verify["permitted_sorries"]
        # The excused declaration is not recorded as verified.
        manifest = load_manifest(root)
        (t1,) = [d for n in manifest.nodes for d in n.declarations if d.name == "t1"]
        (t2,) = [d for n in manifest.nodes for d in n.declarations if d.name == "t2"]
        assert t1.verified_sig is None
        assert t2.verified_sig is not None

    def test_unexcused_sorried_declaration_still_fails(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        sorried_docs = {
            "theorem t1 : 1 = 1": {
                "t1": make_document(
                    "t1", kind="theorem", line_pos=1, end_line_pos=1, is_sorry=True
                )
            },
            "theorem t2 : 1 = 1": {
                "t2": make_document("t2", kind="theorem", line_pos=3, end_line_pos=3)
            },
        }
        fake_axle._extract_documents_by_marker = sorried_docs
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 1
        assert "M.A.t1 FAIL" in " ".join(result.output.split())

    def test_permitted_sorries_outside_the_payload_are_rejected(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(
            main, ["verify", "--select", "M.A", "--permitted-sorries", "M.B.t2"]
        )

        assert result.exit_code == 1
        assert "not part of 'M.A''s payload" in result.output


class TestRitual:
    def test_compile_then_verify_ritual(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """The full offline ritual — compile then verify every target —
        with the project's config plumbing reaching the API."""
        root = make_project(tmp_path, RITUAL_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS

        compile_result = runner.invoke(main, ["compile"])
        assert compile_result.exit_code == 0, compile_result.output
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        assert result.output.count("  OK") == 2
        assert "Verified 2 selection(s): all OK" in result.output
        # The ritual is incremental: the clean compile makes no API
        # calls; each verification is a formal-statement roundtrip plus
        # a verify call carrying the config's global options.
        assert [method for method, _ in fake_axle.calls] == [
            "environments",
            "theorem2sorry",
            "verify_proof",
            "theorem2sorry",
            "verify_proof",
        ]
        assert verify_calls(fake_axle)[0]["global_options"] == {"maxHeartbeats": 100000}

    def test_verify_declaration_selection_ritual(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, RITUAL_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify", "--select", "M.B.t2"])

        assert result.exit_code == 0, result.output
        verify = verify_calls(fake_axle)
        assert len(verify) == 1
        assert verify[0]["formal_statement"] == "formal[t2]"
        # The payload inlines the dependency.
        assert "theorem t1 : 1 = 1 := rfl" in verify[0]["content"]
        assert status_line(result.output, "M.B.t2") == "M.B.t2 OK"


class TestSorry:
    """`--sorry` on verify: stubbed declarations are permitted, and the
    local sorry guard skips them (their `sorry` is ours by construction)."""

    CHAIN_FILES = {
        "M/A.lean": "def base := 1\ntheorem base_holds : base = 1 := rfl\n",
        "M/B.lean": "import A\ntheorem middle : base = 1 := rfl\n",
    }
    # A carries a genuinely sorried declaration: without stubbing it
    # would fail the guard; with --sorry it is stubbed and permitted.
    SORRIED_A_DOCS = {
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
                is_sorry=True,
            ),
        },
        "theorem middle": {
            "middle": make_document(
                "middle",
                kind="theorem",
                line_pos=4,
                end_line_pos=4,
                signature="theorem middle : base = 1",
            ),
        },
    }

    def compile_chain(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> Path:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, self.CHAIN_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.SORRIED_A_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        return root

    def test_sorry_permits_the_stubbed_subtree(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(
            main, ["verify", "--select", "M.B", "--sorry", "M.A"]
        )

        assert result.exit_code == 0, result.output
        # The stubbed declarations (and only they) are permitted; the
        # selection's own theorem stays judged.
        verify = verify_calls(fake_axle)[0]
        assert verify["permitted_sorries"] == ["base", "base_holds"]
        assert status_line(result.output, "M.B") == "M.B OK"

    def test_sorry_guard_skips_stubbed_sorried_declarations(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Without stubbing, A's sorried theorem fails the local guard;
        with `--sorry M.A` it is stubbed by construction and passes."""
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        without = runner.invoke(main, ["verify", "--select", "M.B"])
        assert without.exit_code == 1
        assert "has a `sorry`" in without.output

        result = runner.invoke(
            main, ["verify", "--select", "M.B", "--sorry", "M.A"]
        )

        assert result.exit_code == 0, result.output

    def test_sorry_persists_the_stubbed_payload(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        assert runner.invoke(
            main, ["verify", "--select", "M.B", "--sorry", "M.A"]
        ).exit_code == 0

        persisted = root / ".axbt" / "compiled" / "M_B_stubbed.lean"
        assert persisted.is_file()
        content = persisted.read_text(encoding="utf-8")
        assert "def base : Nat := sorry" in content
        assert "theorem base_holds : base = 1 := by sorry" in content
        # The selection itself is never stubbed.
        assert "theorem middle : base = 1 := rfl" in content

    def test_sorry_on_own_file_stubs_siblings_for_declaration_selections(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Declaration-level verify may stub its own file's siblings;
        the selected theorem keeps its real proof and stays judged."""
        files = {
            "M/A.lean": "def base := 1\ntheorem base_holds : base = 1 := rfl\n",
            "M/B.lean": (
                "import A\ntheorem middle : base = 1 := rfl\n"
                "theorem sibling : base = 1 := rfl\n"
            ),
        }
        docs = {
            **self.SORRIED_A_DOCS,
            "theorem middle": {
                "middle": make_document(
                    "middle",
                    kind="theorem",
                    line_pos=4,
                    end_line_pos=4,
                    signature="theorem middle : base = 1",
                ),
                "sibling": make_document(
                    "sibling",
                    kind="theorem",
                    line_pos=5,
                    end_line_pos=5,
                    signature="theorem sibling : base = 1",
                ),
            },
        }
        root = make_project(tmp_path, NO_TARGETS_CONFIG, files)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = docs
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(
            main, ["verify", "--select", "M.B.middle", "--sorry", "M.B"]
        )

        assert result.exit_code == 0, result.output
        verify = verify_calls(fake_axle)[0]
        # The sibling is stubbed (permitted); the selection is judged.
        assert verify["permitted_sorries"] == ["base_holds", "sibling"]
        assert status_line(result.output, "M.B.middle") == "M.B.middle OK"
        persisted = root / ".axbt" / "compiled" / "M_B_stubbed.lean"
        content = persisted.read_text(encoding="utf-8")
        assert "theorem sibling : base = 1 := by sorry" in content
        assert "theorem middle : base = 1 := rfl" in content

    def test_sorry_naming_only_the_selected_declaration_is_rejected(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)

        result = runner.invoke(
            main, ["verify", "--select", "M.B.middle", "--sorry", "M.B.middle"]
        )

        assert result.exit_code == 1
        assert "never stubbed" in result.output

    def test_sorry_warnings_collapse_into_one_line(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = self.compile_chain(make_project, tmp_path, monkeypatch, fake_axle)
        fake_axle.verify_result = make_response(
            VerifyProofResponse,
            okay=True,
            negation=None,
            lean_messages=Messages(
                [], ["-:1:1-1:20: warning: declaration uses `sorry`"], []
            ),
        )

        result = runner.invoke(
            main, ["verify", "--select", "M.B", "--sorry", "M.A"]
        )

        assert result.exit_code == 0, result.output
        assert "upstream stubbed: 2 declarations" in result.output
        assert "declaration uses" not in result.output


class TestShare:
    """`--share` mints links for submissions and cached verifications."""

    def test_share_prints_links_and_stamps_request_ids(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify", "--share"])

        assert result.exit_code == 0, result.output
        assert len(verify_calls(fake_axle)) == 2
        assert result.output.count("share: https://axle.test/verify_proof#r=fake-req-") == 2
        assert "Share link(s) minted: 2" in result.output
        # Successful verifications record their run's request id.
        manifest = load_manifest(root)
        stamped = {
            d.name: d.verified_request_id
            for n in manifest.nodes
            for d in n.declarations
        }
        assert set(stamped.values()) <= set(fake_axle.request_ids)
        assert all(stamped.values())

    def test_share_links_open_the_verify_route_check_stays_check(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """The two tiers mint differently: a check run's share link
        opens the platform's check UI, a verify run's the verify UI —
        the stored request id already knows what was served; the route
        steers the web page."""
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        check_result = runner.invoke(main, ["check", "--select", "M.A", "--share"])
        assert check_result.exit_code == 0, check_result.output
        assert "share: https://axle.test/check#r=" in check_result.output

        fake_axle.calls.clear()
        verify_result = runner.invoke(main, ["verify", "--select", "M.A", "--share"])
        assert verify_result.exit_code == 0, verify_result.output
        assert "share: https://axle.test/verify_proof#r=" in verify_result.output

    def test_share_on_cached_run_mints_from_the_recorded_run(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        assert runner.invoke(main, ["verify", "--share"]).exit_code == 0
        manifest = load_manifest(root)
        recorded = {
            d.verified_request_id for n in manifest.nodes for d in n.declarations
        }
        minted_before = len(fake_axle.share_requests)
        verify_calls_before = len(verify_calls(fake_axle))

        # Second run: everything cached — the links reference the
        # original verification, no re-submission.
        result = runner.invoke(main, ["verify", "--share"])

        assert result.exit_code == 0, result.output
        assert len(verify_calls(fake_axle)) == verify_calls_before
        assert "(from the earlier run)" in result.output
        minted_ids = [
            rid for _, rid in fake_axle.share_requests[minted_before:]
        ]
        assert set(minted_ids) == recorded

    def test_share_failure_warns_but_leaves_the_exit_code(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.share_status = 404

        result = runner.invoke(main, ["verify", "--share"])

        assert result.exit_code == 0, result.output
        assert "share: unavailable (" in result.output
        assert "Share link(s) minted" not in result.output

    def test_share_sorried_selections_get_no_link(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        sorried_docs = {
            "theorem t1 : 1 = 1": {
                "t1": make_document(
                    "t1", kind="theorem", line_pos=1, end_line_pos=1, is_sorry=True
                )
            },
            "theorem t2 : 1 = 1": {
                "t2": make_document("t2", kind="theorem", line_pos=3, end_line_pos=3)
            },
        }
        fake_axle._extract_documents_by_marker = sorried_docs
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify", "--share"])

        # t1's guard failure fails the run; only the sibling t2
        # submitted, so exactly one link exists.
        assert result.exit_code == 1
        assert result.output.count("share: https://axle.test/verify_proof#r=") == 1


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
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        # A's own-file marker routes the delay to A only; the marker
        # routing picks the one occurring latest in a payload, and B's
        # payload (dependencies inlined) ends with `theorem t2`.
        fake_axle.verify_delays = {"theorem t1 : 1 = 1": 0.15, "theorem t2 : 1 = 1": 0.0}

        result = runner.invoke(main, ["verify"])

        assert result.exit_code == 0, result.output
        streamed = [
            line
            for line in result.output.splitlines()
            if _TIMESTAMP.match(line) and re.match(r"\[\s*\d/\d\]", line.split()[1])
            and "START" not in line
        ]
        # B completes first and streams first, each verdict line numbered
        # by its item (B is selection 2, A is 1) with the total 2.
        assert ["M.B.t2", "M.A.t1"] == [line.split()[2] for line in streamed]
        for line in streamed:
            assert re.search(r"\d+\.\d{3}s$", line), line
        def _delay(line: str) -> float:
            return float(line.split()[-1].removesuffix("s"))
        # A carried the artificial delay; the timing is per item, not
        # the whole run.
        assert _delay(streamed[1]) > _delay(streamed[0])
        assert re.search(r"Verified 2 selection\(s\): all OK in \d+\.\d{3}s", result.output)


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
        "M/A.lean": "theorem t1 : 1 = 1 := rfl\n",
        "M/B.lean": "import A\ntheorem t2 : 1 = 1 := rfl\n",
        "M/C.lean": "import A\nimport B\ntheorem t3 : 1 = 1 := rfl\n",
    }

    DOCS = {
        "theorem t1 : 1 = 1": {
            "t1": make_document("t1", kind="theorem", line_pos=1, end_line_pos=1)
        },
        "theorem t2 : 1 = 1": {
            "t2": make_document("t2", kind="theorem", line_pos=3, end_line_pos=3)
        },
        "theorem t3 : 1 = 1": {
            "t3": make_document("t3", kind="theorem", line_pos=5, end_line_pos=5)
        },
    }

    def test_first_failure_cancels_in_flight_submissions(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """The failing result streams first and cuts the run short.

        The first failure is reported with its timing; submissions
        still in flight are cancelled rather than finished, and the
        summary accounts for what was not judged.
        """
        root = make_project(tmp_path, self.TARGETS_CONFIG, self.FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()
        fake_axle.request_ids.clear()
        fake_axle.verify_result = make_response(
            VerifyProofResponse, okay=False, negation=None
        )
        fake_axle.verify_delays = {"theorem t2 : 1 = 1": 0.5, "theorem t3 : 1 = 1": 0.5}

        result = runner.invoke(main, ["verify", "-x"])

        assert result.exit_code == 1, result.output
        # The delayed submissions were cancelled in flight (t1's formal
        # statement roundtrip completed; its verify never returned for
        # the others).
        assert len(fake_axle.request_ids) == 1
        streamed = [
            line
            for line in result.output.splitlines()
            if _TIMESTAMP.match(line) and re.match(r"\[\s*\d/\d\]", line.split()[1])
            and "START" not in line
        ]
        assert len(streamed) == 1
        assert "M.A.t1" in streamed[0]
        assert "FAIL" in streamed[0]
        assert "fail-fast: cancelled 2 remaining selection(s)" in result.output
        assert re.search(
            r"Verified 3 selection\(s\): 1 failed, 0 OK, "
            r"2 cancelled by fail-fast in \d+\.\d{3}s",
            result.output,
        )

    def test_sorried_local_failure_stops_before_any_submission(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A `sorry` failure cuts the run off before any submission.

        The local sorry guard reports the first failing selection with
        no API calls at all, and the remaining selections report as
        cancelled.
        """
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "theorem t1 : 1 = 1": {
                "t1": make_document(
                    "t1", kind="theorem", line_pos=1, end_line_pos=1, is_sorry=True
                )
            },
            "theorem t2 : 1 = 1": {
                "t2": make_document("t2", kind="theorem", line_pos=3, end_line_pos=3)
            },
        }
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["verify", "--fail-fast"])

        assert result.exit_code == 1, result.output
        # Failed locally: no submissions at all ran (the environment
        # resolution upfront is the only API touch).
        assert not [
            m for m, _ in fake_axle.calls if m in ("theorem2sorry", "verify_proof")
        ]
        assert status_line(result.output, "M.A.t1") == "M.A.t1 FAIL"
        assert "fail-fast: cancelled 1 remaining selection(s)" in result.output
        assert re.search(
            r"Verified 2 selection\(s\): 1 failed, 0 OK, "
            r"1 cancelled by fail-fast in \d+\.\d{3}s",
            result.output,
        )

    def test_fail_fast_leaves_happy_runs_untouched(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, TARGETS_CONFIG, THEOREM_FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = THEOREM_DOCS
        assert runner.invoke(main, ["compile"]).exit_code == 0

        result = runner.invoke(main, ["verify", "--fail-fast"])

        assert result.exit_code == 0, result.output
        assert "Verified 2 selection(s): all OK" in result.output
