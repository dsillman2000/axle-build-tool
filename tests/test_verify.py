"""CLI-level tests for `axbt verify`, driven through the real entry point."""

from __future__ import annotations

import shutil
from pathlib import Path

from axle.types import Messages, VerifyProofNegation, VerifyProofResponse
from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.manifest import load_manifest
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
        first, second = verify_calls(fake_axle)
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
        assert len(verify_calls(fake_axle)) == 2

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
        # No names: the formal statement covers the whole payload, and
        # nothing is excused — file-level verify is strict over the
        # payload's every theorem.
        assert sorry_calls[0]["names"] is None
        assert verify_calls(fake_axle)[0]["formal_statement"] == "formal[all]"
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
        assert fake_axle.calls == []
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
        # Failed locally: not even the formal-statement roundtrip ran.
        assert fake_axle.calls == []
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
