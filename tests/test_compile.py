"""CLI-level tests for `axbt compile`, driven through the real entry point.

All compiles run against a faked Axle client (wired in automatically via
the `offline_axle` fixture) so the suite never touches the network.
"""

from __future__ import annotations

import hashlib
import json
import shutil
from pathlib import Path

import pytest
from axle.exceptions import AxleApiError
from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.manifest import (
    MANIFEST_FILENAME,
    MANIFEST_VERSION,
    load_manifest,
    manifest_path,
)
from conftest import make_document, make_extract_response, start_line, status_line, stripped_lines

runner = CliRunner()

SIMPLE_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""


@pytest.fixture(autouse=True)
def offline_axle(fake_axle):
    """Every compile in this module runs against a faked Axle client."""
    return fake_axle


def extract_calls(fake) -> int:
    return sum(1 for method, _ in fake.calls if method == "extract_decls")


SIMPLE_FILES = {"M/A.lean": "def x := 1\n", "M/B.lean": "import A\ndef y := x\n"}

# An import-only aggregate: a docstring plus imports, no declaration
# keyword anywhere in the source.
AGGREGATE_FILES = {
    "M/A.lean": "def x := 1\n",
    "M/B.lean": "import A\ndef y := x\n",
    "M/Agg.lean": (
        "\n/-! # Aggregate\n\n"
        "A one-line import for the whole module area; declarations live\n"
        "in their own files. -/\n"
        "import A\n"
        "import B\n"
    ),
}

# A file with no actual declarations whose docstring *mentions* one —
# the conservative direction keeps it in the extraction flow.
DOCSTRING_MENTION_FILES = {
    **SIMPLE_FILES,
    "M/Doc.lean": (
        "\n/-! # Notes\n\n"
        "The `def` of nothing appears in this docstring only; the file\n"
        "declares nothing itself. -/\n"
    ),
}


class TestHelp:
    def test_help_lists_init_and_compile(self) -> None:
        result = runner.invoke(main, ["--help"])
        assert result.exit_code == 0
        assert "init" in result.output
        assert "compile" in result.output


class TestCompileProject:
    def test_compile_creates_manifest(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, SIMPLE_FILES)
        monkeypatch.chdir(root)
        assert not (root / ".axbt").exists()

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert manifest_path(root).is_file()

    def test_manifest_shape(self, make_project, tmp_path: Path, monkeypatch) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, SIMPLE_FILES)
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        raw = json.loads(manifest_path(root).read_text(encoding="utf-8"))
        assert set(raw) == {"version", "generated_at", "nodes"}
        assert raw["version"] == MANIFEST_VERSION
        names = {node["name"] for node in raw["nodes"]}
        assert names == {"M.A", "M.B"}
        # And it still loads through our own loader.
        assert len(load_manifest(root).nodes) == 2

    def test_diamond_dag_edges(self, make_project, tmp_path: Path, monkeypatch) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {
                "M/A.lean": "def x := 1\n",
                "M/B.lean": "import A\ndef y := x\n",
                "M/C.lean": "import A\nimport B\ndef z := y + x\n",
            },
        )
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        by_name = load_manifest(root).by_name()
        a, b, c = by_name["M.A"], by_name["M.B"], by_name["M.C"]

        assert a.parents == []
        assert b.parents == ["M.A"]
        assert c.parents == ["M.A", "M.B"]
        # children are the inverse of parents
        assert a.children == ["M.B", "M.C"]
        assert c.children == []

    def test_md5_fingerprints(self, make_project, tmp_path: Path, monkeypatch) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, SIMPLE_FILES)
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        for node in load_manifest(root).nodes:
            data = (root / node.path).read_bytes()
            assert node.md5 == hashlib.md5(data).hexdigest()

    def test_default_dir_rule(self, make_project, tmp_path: Path, monkeypatch) -> None:
        """A module without `dir` scans the module-name directory."""
        config = """\
project:
  name: proj
modules:
  Solo:
    targets: []
"""
        root = make_project(tmp_path, config, {"Solo/Solo.lean": "def x := 1\n"})
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        manifest = load_manifest(root)
        assert [node.name for node in manifest.nodes] == ["Solo.Solo"]
        assert manifest.nodes[0].parents == []


class TestCompileBehavior:
    def test_first_run_new_then_recompile_clean(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {
                "M/A.lean": "def x := 1\n",
                "M/B.lean": "import A\ndef y := x\n",
            },
        )
        monkeypatch.chdir(root)

        first = runner.invoke(main, ["compile"])
        assert first.exit_code == 0, first.output
        m1 = load_manifest(root)
        assert {node.status for node in m1.nodes} == {"new"}

        second = runner.invoke(main, ["compile"])
        assert second.exit_code == 0, second.output
        m2 = load_manifest(root)
        assert {node.status for node in m2.nodes} == {"clean"}
        fingerprint = lambda m: [
            (n.name, n.md5, tuple(n.parents), tuple(n.children)) for n in m.nodes
        ]
        assert fingerprint(m1) == fingerprint(m2)

    def test_edit_delete_add_lifecycle(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {
                "M/A.lean": "def x := 1\n",
                "M/B.lean": "import A\ndef y := x\n",
            },
        )
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        # Editing A changes A; B's bytes are untouched.
        (root / "M/A.lean").write_text("def x := 2\n", encoding="utf-8")
        assert runner.invoke(main, ["compile"]).exit_code == 0
        after_edit = load_manifest(root)
        assert after_edit.by_name()["M.A"].status == "changed"
        assert after_edit.by_name()["M.B"].status == "clean"

        # Deleting B drops its node.
        (root / "M/B.lean").unlink()
        assert runner.invoke(main, ["compile"]).exit_code == 0
        after_delete = load_manifest(root)
        assert "M.B" not in after_delete.by_name()

        # Adding C appears as a new node.
        (root / "M/C.lean").write_text("def z := 3\n", encoding="utf-8")
        assert runner.invoke(main, ["compile"]).exit_code == 0
        after_add = load_manifest(root)
        assert after_add.by_name()["M.C"].status == "new"

    def test_import_cycle_fails_and_leaves_manifest_intact(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {
                "M/A.lean": "def x := 1\n",
                "M/B.lean": "def y := 2\n",
            },
        )
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0
        before = manifest_path(root).read_bytes()

        (root / "M/A.lean").write_text("import B\ndef x := 1\n", encoding="utf-8")
        (root / "M/B.lean").write_text("import A\ndef y := 2\n", encoding="utf-8")
        result = runner.invoke(main, ["compile"])

        assert result.exit_code != 0
        assert "cycle" in result.output.lower()
        assert manifest_path(root).read_bytes() == before

    def test_self_import_fails(self, make_project, tmp_path: Path, monkeypatch) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, {"M/A.lean": "import A\n"})
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code != 0
        assert "cycle" in result.output.lower()

    def test_ambiguous_import_fails_naming_candidates(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(
            tmp_path,
            "modules:\n  M:\n    targets: []\n  N:\n    targets: []\n  P:\n    targets: []\n",
            {
                "M/A.lean": "def m := 1\n",
                "N/A.lean": "def n := 1\n",
                "P/B.lean": "import A\ndef b := 1\n",
            },
        )
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code != 0
        assert "ambiguous" in result.output
        assert "M.A" in result.output and "N.A" in result.output

    def test_dangling_target_fails_naming_target(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(
            tmp_path,
            "modules:\n  M:\n    targets:\n      - Missing.thm\n",
            {"M/A.lean": "def x := 1\n"},
        )
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code != 0
        assert "Missing.thm" in result.output

    def test_compile_outside_project_fails(self, tmp_path: Path, monkeypatch) -> None:
        monkeypatch.chdir(tmp_path)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code != 0
        assert "axbt_project.yml" in result.output

    def test_missing_module_dir_fails(self, make_project, tmp_path: Path, monkeypatch) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, files={})
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code != 0
        assert "does not exist" in result.output

    def test_empty_module_dir_is_only_a_note(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, files={})
        (root / "M").mkdir()
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert "no .lean files" in result.output
        assert load_manifest(root).nodes == []


class TestDeclarationFreeNodes:
    """Import-only aggregate files (docstring plus imports, no
    declaration keyword anywhere) skip their extraction request: they'd
    otherwise pay a full dependency-closure extraction payload for an
    empty document set. Detection errs toward extraction."""

    def test_aggregate_skips_extraction_and_is_recorded_empty(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, AGGREGATE_FILES)
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert extract_calls(fake_axle) == 2  # A and B only; Agg skipped
        manifest = load_manifest(root)
        aggregate = next(node for node in manifest.nodes if node.name == "M.Agg")
        assert aggregate.declarations == []
        assert aggregate.request_id is None

    def test_skipped_aggregate_carries_over_clean(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A second compile makes no extraction calls at all: the
        skipped node's recorded (empty) metadata is carried over by MD5
        like any extracted node's."""
        root = make_project(tmp_path, SIMPLE_CONFIG, AGGREGATE_FILES)
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0
        fake_axle.calls.clear()

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert extract_calls(fake_axle) == 0

    def test_docstring_mention_still_extracts(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A file with no declarations whose docstring mentions `def`
        keeps its extraction request (the conservative direction: never
        skip a file that could have declarations)."""
        root = make_project(tmp_path, SIMPLE_CONFIG, DOCSTRING_MENTION_FILES)
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert extract_calls(fake_axle) == 3
        submitted_content = [
            kwargs["content"]
            for method, kwargs in fake_axle.calls
            if method == "extract_decls"
        ]
        assert any("declares nothing itself" in content for content in submitted_content)


class TestExtraction:
    """Scope B: compile enriches the manifest with Axle-extracted
    declaration metadata, incrementally."""

    def test_nodes_get_declaration_metadata(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Positions are attributed back to file coordinates: A's files
        carry a hoisted import and docstring shift; B's declaration maps
        through the inlined dependency geometry."""
        files = {
            "M/A.lean": (
                "import Mathlib\n\n/-! Base. -/\n\ndef base := 1\n"
                "theorem base_thm : base = 1 := rfl\n"
            ),
            "M/B.lean": "import A\ntheorem middle_thm : base = 1 := rfl\n",
        }
        docs = {
            "def base := 1": {
                "base": make_document("base", kind="def", line_pos=6, end_line_pos=6),
                "base_thm": make_document(
                    "base_thm",
                    kind="theorem",
                    line_pos=7,
                    end_line_pos=7,
                    signature="theorem base_thm : base = 1 := rfl",
                ),
            },
            "theorem middle_thm": {
                "middle_thm": make_document(
                    "middle_thm", kind="theorem", line_pos=9, end_line_pos=9
                )
            },
        }
        fake_axle._extract_documents_by_marker = docs
        root = make_project(tmp_path, SIMPLE_CONFIG, files)
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        manifest = load_manifest(root)
        a = manifest.by_name()["M.A"]
        assert [d.name for d in a.declarations] == ["base", "base_thm"]
        assert a.declarations[0].kind == "def"
        assert a.declarations[0].is_sorry is False
        # def base sits at file line 5: payload line 6 mapped back
        # through the hoisted import header and docstring shift.
        assert a.declarations[0].line_pos == 5
        assert a.declarations[1].line_pos == 6
        assert a.declarations[1].signature.startswith("theorem base_thm")
        b = manifest.by_name()["M.B"]
        assert [d.name for d in b.declarations] == ["middle_thm"]
        # middle_thm is file line 2 (its import was stripped from the
        # payload; A's five kept lines and a separator sit above it).
        assert b.declarations[0].line_pos == 2

    def test_sorry_flag_is_recorded(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> None:
        from conftest import make_extract_response

        fake_axle._extract_documents = {
            "open_problem": make_document("open_problem", is_sorry=True, line_pos=1, end_line_pos=1)
        }
        root = make_project(tmp_path, SIMPLE_CONFIG, {"M/A.lean": "theorem open_problem : P := by sorry\n"})
        monkeypatch.chdir(root)

        assert runner.invoke(main, ["compile"]).exit_code == 0

        (node,) = load_manifest(root).nodes
        assert node.declarations[0].is_sorry is True

    def test_compilation_gcs_payload_artifacts_of_dropped_nodes(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> None:
        """Deleting a source file and recompiling prunes its `.axbt/compiled/`
        payloads — stale module-slug files must not survive the manifest
        rewrite (issue 43). Live stubbed and module-level variants of
        *live* nodes, and failing submissions under `.axbt/failed/`, stay.
        """
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {
                "M/A.lean": "def x := 1\n",
                "M/B.lean": "theorem y : True := rfl\n",
            },
        )
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "def x := 1": {
                "x": make_document("x", kind="def", line_pos=1, end_line_pos=1)
            },
            "theorem y": {
                "y": make_document("y", kind="theorem", line_pos=1, end_line_pos=1)
            },
        }
        assert runner.invoke(main, ["compile"]).exit_code == 0
        compiled = root / ".axbt" / "compiled"
        assert (compiled / "M_A_isolated.lean").is_file()
        assert (compiled / "M_B_isolated.lean").is_file()

        # Stale candidates plus kept artifacts: the dropped node's stubbed
        # variant, a module-level stubbed variant (module still live), and
        # a failing submission under `.axbt/failed/`.
        (compiled / "M_B_stubbed.lean").write_text("stubbed\n", encoding="utf-8")
        (compiled / "M_stubbed.lean").write_text("stubbed\n", encoding="utf-8")
        failed = root / ".axbt" / "failed"
        failed.mkdir(parents=True, exist_ok=True)
        (failed / "req-1.lean").write_text("payload\n", encoding="utf-8")
        (root / "M" / "B.lean").unlink()

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert load_manifest(root).by_name().keys() == {"M.A"}
        assert (compiled / "M_A_isolated.lean").is_file()
        assert not (compiled / "M_B_isolated.lean").exists()
        assert not (compiled / "M_B_stubbed.lean").exists()
        # Module M is still live, so its per-selection stubbed payload stays —
        # and `.axbt/failed/` is a sibling of the swept directory.
        assert (compiled / "M_stubbed.lean").is_file()
        assert (failed / "req-1.lean").is_file()
        assert "Pruned 2 stale payload file(s)" in result.output
        assert (
            ".axbt/compiled/M_B_isolated.lean, .axbt/compiled/M_B_stubbed.lean"
            in result.output
        )

    def test_compilation_without_dead_artifacts_makes_no_prune_note(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> None:
        root = make_project(
            tmp_path, SIMPLE_CONFIG, {"M/A.lean": "def x := 1\n"}
        )
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "def x := 1": {
                "x": make_document("x", kind="def", line_pos=1, end_line_pos=1)
            },
        }

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert "Pruned" not in result.output

    def test_declaration_dependencies_are_recorded(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Each extracted declaration carries its dependency lists: the
        local type/value/syntactic variants union into one deduplicated,
        sorted `dependencies` list, and the external variants persist
        separately (tooltip material, not graph nodes)."""
        files = {"M/A.lean": "def base := 1\ntheorem derived : base = 1 := rfl\n"}
        docs = {
            "theorem derived": {
                "base": make_document("base", kind="def", line_pos=1, end_line_pos=1),
                "derived": make_document(
                    "derived",
                    kind="theorem",
                    line_pos=2,
                    end_line_pos=2,
                    local_type_dependencies=["base"],
                    local_value_dependencies=["base", "Eq", "Nat"],
                    local_syntactic_dependencies=["rfl"],
                    external_type_dependencies=["Nat"],
                    external_value_dependencies=["Nat", "Eq"],
                ),
            },
        }
        fake_axle._extract_documents_by_marker = docs
        root = make_project(tmp_path, SIMPLE_CONFIG, files)
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        (node,) = load_manifest(root).nodes
        base, derived = node.declarations
        assert base.dependencies == []
        assert base.external_dependencies == []
        assert derived.dependencies == ["Eq", "Nat", "base", "rfl"]
        assert derived.external_dependencies == ["Eq", "Nat"]

    def test_cross_file_dependencies_survive_signature_stubs(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Extraction submits the node's dependency closure with every
        other file's proof/definition bodies stubbed to signatures; the
        dependency names the API reports for the node's own documents
        are recorded as-is, so a node referencing its import's
        declarations still carries the cross-file edge."""
        files = {
            "M/A.lean": "def base := 1\n",
            "M/B.lean": "import A\ntheorem derived : base = 1 := rfl\n",
        }
        docs = {
            "def base := 1": {
                "base": make_document(
                    "base",
                    kind="def",
                    line_pos=1,
                    end_line_pos=1,
                    signature="def base",
                ),
            },
            "theorem derived": {
                "derived": make_document(
                    "derived", kind="theorem", line_pos=3, end_line_pos=3
                ),
            },
        }
        fake_axle._extract_documents_by_marker = docs
        root = make_project(tmp_path, SIMPLE_CONFIG, files)
        monkeypatch.chdir(root)

        assert runner.invoke(main, ["compile"]).exit_code == 0

        # Re-extract just B (A stays clean): B's payload now inlines A
        # with base's real body (def bodies survive stubbing), the very
        # situation the manifest's dependency names must stay true to.
        (root / "M/B.lean").write_text(
            "import A\ntheorem derived : base = 1 := rfl\n-- touched\n",
            encoding="utf-8",
        )
        fake_axle._extract_documents_by_marker["-- touched"] = {
            "derived": make_document(
                "derived",
                kind="theorem",
                line_pos=3,
                end_line_pos=3,
                local_syntactic_dependencies=["base"],
            ),
        }
        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        manifest = load_manifest(root)
        (derived,) = manifest.by_name()["M.B"].declarations
        assert derived.dependencies == ["base"]
        assert manifest.by_name()["M.A"].declarations[0].name == "base"
        # A's own record keeps no deps (a dependency-free file).
        assert manifest.by_name()["M.A"].declarations[0].dependencies == []

    def test_recompile_skips_extraction(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {"M/A.lean": "def x := 1\n", "M/B.lean": "import A\ndef y := x\n"},
        )
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0
        first = load_manifest(root)
        calls_after_first = extract_calls(fake_axle)
        assert calls_after_first == 2

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert extract_calls(fake_axle) == calls_after_first  # zero new calls
        assert "0 extracted now, 2 carried over" in result.output
        second = load_manifest(root)
        assert second.by_name()["M.A"].declarations == first.by_name()["M.A"].declarations

    def test_edit_reextracts_only_the_changed_file(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {"M/A.lean": "def x := 1\n", "M/B.lean": "import A\ndef y := x\n"},
        )
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0
        first = load_manifest(root)
        calls_after_first = extract_calls(fake_axle)
        first_node_ids = {node.name: node.request_id for node in first.nodes}

        (root / "M/A.lean").write_text("def x := 2\n", encoding="utf-8")
        assert runner.invoke(main, ["compile"]).exit_code == 0

        assert extract_calls(fake_axle) == calls_after_first + 1  # only A
        second = load_manifest(root)
        assert second.by_name()["M.A"].status == "changed"
        # A was re-extracted: fresh request id; B's provenance is untouched.
        assert second.by_name()["M.A"].request_id != first_node_ids["M.A"]
        assert second.by_name()["M.B"].request_id == first_node_ids["M.B"]
        # B's data is carried over untouched.
        assert second.by_name()["M.B"].declarations == first.by_name()["M.B"].declarations

    def test_transport_failure_names_file_and_keeps_manifest_intact(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, {"M/A.lean": "def x := 1\n"})
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0
        before = manifest_path(root).read_bytes()

        # Change the source so the node needs extraction, then make Axle fail.
        (root / "M/A.lean").write_text("def x := 2\n", encoding="utf-8")
        fake_axle._error = AxleApiError("backend exploded")
        result = runner.invoke(main, ["compile"])

        assert result.exit_code != 0
        assert "M/A.lean" in result.output
        assert "Axle API error" in result.output
        assert manifest_path(root).read_bytes() == before

    def test_lean_errors_in_response_fail_extraction(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, {"M/A.lean": "def x := 1\n"})
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0
        before = manifest_path(root).read_bytes()

        # Change the source so the node needs extraction; the canned Axle
        # response then reports Lean errors, which must fail the compile.
        (root / "M/A.lean").write_text("def x := 2\n", encoding="utf-8")
        fake_axle._extract_lean_errors.append("syntax error at line 3")
        result = runner.invoke(main, ["compile"])

        assert result.exit_code != 0
        assert "M/A.lean" in result.output
        assert "syntax error at line 3" in result.output
        assert manifest_path(root).read_bytes() == before

    def test_multiple_failures_are_all_reported(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {"M/A.lean": "def x := 1\n", "M/B.lean": "def y := 2\n"},
        )
        monkeypatch.chdir(root)
        fake_axle._error = AxleApiError("backend exploded")

        result = runner.invoke(main, ["compile"])

        assert result.exit_code != 0
        assert "M/A.lean" in result.output
        assert "M/B.lean" in result.output

    def test_extracted_nodes_record_axle_request_ids(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """Each node's manifest entry carries the request id of the API call
        that produced its data; carried-over nodes keep their original id."""
        files = {
            "M/A.lean": "def x := 1\n",
            "M/B.lean": "import A\ndef y := x\n",
            "M/C.lean": "import B\ndef z := y\n",
        }
        docs = {
            "def x := 1": {
                "x": make_document("x", kind="def", line_pos=1, end_line_pos=1)
            },
            "def y := x": {
                "y": make_document("y", kind="def", line_pos=3, end_line_pos=3)
            },
            "def z := y": {
                "z": make_document("z", kind="def", line_pos=3, end_line_pos=3)
            },
        }
        fake_axle._extract_documents_by_marker = docs
        root = make_project(tmp_path, SIMPLE_CONFIG, files)
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        first = load_manifest(root)
        assert all(node.request_id is not None for node in first.nodes)
        assert len({node.request_id for node in first.nodes}) == 3  # distinct calls
        assert set(first_node_ids := {node.request_id for node in first.nodes}) == set(
            fake_axle.request_ids
        )

        # A recompile carries the same provenance (no new requests).
        assert runner.invoke(main, ["compile"]).exit_code == 0
        assert load_manifest(root).nodes[0].request_id in first_node_ids

    def test_stale_version_manifest_is_ignored_and_reextracted(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, {"M/A.lean": "def x := 1\n"})
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        # A manifest written by an incompatible schema version carries no
        # usable contract: it must be ignored (fully re-extracted), not
        # partially trusted.
        raw = json.loads(manifest_path(root).read_text(encoding="utf-8"))
        raw["version"] = MANIFEST_VERSION + 99
        manifest_path(root).write_text(json.dumps(raw, indent=2), encoding="utf-8")

        calls_before = extract_calls(fake_axle)
        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert extract_calls(fake_axle) == calls_before + 1
        rewritten = load_manifest(root)
        assert rewritten.version == MANIFEST_VERSION


class TestCompiledPayloads:
    """Scope C: compile persists per-file isolated payloads for inspection."""

    def test_compile_writes_isolated_payloads(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        fake_axle._extract_documents_by_marker = {
            "def base := 1": {
                "base": make_document("base", kind="def", line_pos=3, end_line_pos=3)
            },
            "def middle := base": {
                "middle": make_document(
                    "middle", kind="def", line_pos=5, end_line_pos=5
                )
            },
        }
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {
                "M/A.lean": "import Mathlib\ndef base := 1\n",
                "M/B.lean": "import A\nimport Mathlib\ndef middle := base + 1\n",
            },
        )
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        compiled = root / ".axbt" / "compiled"
        assert sorted(p.name for p in compiled.iterdir()) == [
            "M_A_isolated.lean",
            "M_B_isolated.lean",
        ]

        b_payload = (compiled / "M_B_isolated.lean").read_text(encoding="utf-8")
        # Dependencies are inlined before the target file...
        assert b_payload.index("def base := 1") < b_payload.index("def middle")
        # ...intra-project imports are replaced by the inlined content...
        assert "import A" not in b_payload
        # ...and external imports are hoisted to the top exactly once.
        assert b_payload.count("import Mathlib") == 1
        assert b_payload.splitlines()[0] == "import Mathlib"

    def test_recompile_rewrites_payloads_idempotently(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, {"M/A.lean": "def x := 1\n"})
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0
        first = (root / ".axbt" / "compiled" / "M_A_isolated.lean").read_text(
            encoding="utf-8"
        )

        assert runner.invoke(main, ["compile"]).exit_code == 0

        assert (
            root / ".axbt" / "compiled" / "M_A_isolated.lean"
        ).read_text(encoding="utf-8") == first


class TestFailedExtractionPersistence:
    """A failed node's extraction payload is persisted like a failing
    submission — `.axbt/failed/<id>.lean` (+ `.map.json`) with the
    `extract` tier — and the error listing names the saved paths.

    Nothing else survives a failed compile (the manifest is
    all-or-nothing), so this is the only autopsy surface for extraction
    diagnostics quoting payload coordinates.
    """

    FILES = {
        "M/A.lean": "def x := 1\n",
        "M/B.lean": "import A\n\ntheorem y : x = x := by\n  rw [x]\n",
    }
    DOCS = {
        "def x := 1": {
            "x": make_document("x", kind="def", line_pos=1, end_line_pos=1)
        },
        "theorem y : x = x": {
            "y": make_document(
                "y",
                kind="theorem",
                line_pos=4,
                end_line_pos=4,
                local_value_dependencies=["x"],
            )
        },
    }

    @staticmethod
    def probe(make_project, tmp_path: Path, monkeypatch, fake_axle):
        root = make_project(tmp_path, SIMPLE_CONFIG, TestFailedExtractionPersistence.FILES)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = TestFailedExtractionPersistence.DOCS
        return root

    def test_lean_error_extraction_persists_payload_and_maps(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        import json as jsonlib

        root = self.probe(make_project, tmp_path, monkeypatch, fake_axle)
        fake_axle._extract_lean_errors = ["-:3:5: error: unknown identifier 'x'"]

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 1, result.output
        # Error lines name the persisted artifacts per failed node.
        assert ".axbt/failed/" in result.output
        assert "error: unknown identifier" in result.output
        failed_dir = root / ".axbt" / "failed"
        lean_files = sorted(failed_dir.glob("*.lean"))
        # Both filesystems failed (the fixture's errors apply to every
        # extraction call): one pair per node's own extraction payload.
        assert [p.name for p in lean_files], result.output
        for lean_file in lean_files:
            stem = lean_file.name[: -len(".lean")]
            mapped = jsonlib.loads(
                (failed_dir / f"{stem}.map.json").read_text(encoding="utf-8")
            )
            assert mapped["tier"] == "extract"
        # Each pair keyed on its own extraction's request id.
        assert {
            jsonlib.loads(
                (failed_dir / f"{p.name[:-len('.lean')]}.map.json").read_text(
                    encoding="utf-8"
                )
            )["request_id"]
            for p in lean_files
        } == set(fake_axle.request_ids)
        # The inlined payload shape survived: A's pair maps its own
        # section alone; B's pair also carries A's inlined (stubbed)
        # section above it.
        by_request = {
            m["request_id"]: m
            for m in (
                jsonlib.loads(
                    (failed_dir / f"{p.name[:-len('.lean')]}.map.json").read_text(
                        encoding="utf-8"
                    )
                )
                for p in lean_files
            )
        }
        assert by_request[fake_axle.request_ids[0]]["sections"] == {"M.A": [1, 1]}
        assert by_request[fake_axle.request_ids[1]]["sections"] == {
            "M.A": [1, 1],
            "M.B": [3, 5],
        }

    def test_call_error_extraction_persists_with_timestamp_stem(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = self.probe(make_project, tmp_path, monkeypatch, fake_axle)
        from axle_build_tool.axle_service import AxleServiceError

        fake_axle.extract_error = AxleServiceError("connection reset by peer")

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 1, result.output
        failed_dir = root / ".axbt" / "failed"
        pairs = sorted(failed_dir.glob("*"))
        # Two failed nodes: two persisted pairs, named with the noid
        # fallback (no response, so the id-keyed stem cannot be minted).
        assert len([p for p in pairs if p.name.endswith(".lean")]) == 2, (
            [p.relative_to(root).as_posix() for p in pairs]
        )
        # The failing result names the saved artifact paths.
        assert "(payload saved: .axbt/failed/noid-" in result.output


class TestExtractionProgress:
    """The compile stage streams dbt-style progress: per-node START at
    dispatch, verdicts with measured durations at completion (completion
    order), and dim SKIP lines for declaration-free nodes — so a slow
    extraction's wall time is visible while the run lives.
    """

    DOCS = {
        "def x := 1": {
            "x": make_document("x", kind="def", line_pos=1, end_line_pos=1)
        },
        "theorem y : x = x": {
            "y": make_document(
                "y",
                kind="theorem",
                line_pos=4,
                end_line_pos=4,
                local_value_dependencies=["x"],
            )
        },
    }

    @staticmethod
    def strip_timing(line: str) -> str:
        """A streamed row without its trailing measured duration."""
        import re

        return re.sub(r" \d+\.\d{3}s$", "", line)

    def test_started_lines_and_durations_are_streamed(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> None:
        files = {"M/A.lean": "def x := 1\n", "M/B.lean": "import A\ntheorem y : x = x := by\n  rw [x]\n"}
        root = make_project(tmp_path, SIMPLE_CONFIG, files)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.DOCS
        # B's payload contains A's source (inlined last), so the marker
        # routes 'def x' to whichever payload mentions it LATER — make
        # A fast and B slow by routing on B's own line.
        fake_axle.extract_delays = {"theorem y : x = x": 0.15}

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        # START lines at the same counter their verdicts pair under.
        assert start_line(result.output, "M.A") == "M.A START [RUN]"
        assert start_line(result.output, "M.B") == "M.B START [RUN]"
        assert status_line(result.output, "M.A") == "M.A OK"
        assert status_line(result.output, "M.B") == "M.B OK"
        # Durations are printed on every verdict row.
        ok_rows = [line for line in result.output.splitlines() if " OK  " in line]
        assert len(ok_rows) == 2
        assert all(row.rstrip().endswith("s") for row in ok_rows)
        # Completion order streams A first (B pays the artificial delay).
        verdicts = [self.strip_timing(line) for line in stripped_lines(result.output)]
        assert verdicts.index("M.A OK") < verdicts.index("M.B OK")

    def test_declaration_free_nodes_report_skips(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {
                "M/A.lean": "def x := 1\n",
                "M/Agg.lean": "\n/-! # Aggregate -/\nimport A\n",
            },
        )
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "def x := 1": {
                "x": make_document("x", kind="def", line_pos=1, end_line_pos=1)
            }
        }

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        normalized = stripped_lines(result.output)
        assert "M.Agg SKIP" in normalized
        assert any("declaration-free" in line for line in normalized)
        # The aggregate made no extraction call and shows no START.
        with pytest.raises(AssertionError):
            start_line(result.output, "M.Agg")

    def test_failed_extraction_streams_fail_rows_with_durations(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> None:
        import json as jsonlib

        files = {"M/A.lean": "def x := 1\n", "M/B.lean": "import A\ntheorem y : x = x := by\n  rw [x]\n"}
        root = make_project(tmp_path, SIMPLE_CONFIG, files)
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = self.DOCS
        fake_axle._extract_lean_errors = ["-:3:5: error: unknown identifier 'x'"]

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 1, result.output
        # Verdict rows carry their durations; the timing-stripped stream
        # has a FAIL row for every failing node's own counter.
        verdicts = [self.strip_timing(line) for line in stripped_lines(result.output)]
        assert "M.A FAIL" in verdicts
        assert "M.B FAIL" in verdicts
        # The verdict reason, with the persisted-payload reference.
        assert any("error: unknown identifier" in line for line in verdicts + stripped_lines(result.output))
        assert any("payload saved: .axbt/failed/" in line for line in verdicts + stripped_lines(result.output))
        # The end-of-run listing survives alongside the streaming rows.
        assert "Failed to extract declarations:" in result.output
        # The persisted map of the failing node still parses.
        failed_dir = root / ".axbt" / "failed"
        pairs = sorted(failed_dir.glob("*.map.json"))
        assert [p.name for p in pairs]
        for pair in pairs:
            assert jsonlib.loads(pair.read_text(encoding="utf-8"))["tier"] == "extract"
