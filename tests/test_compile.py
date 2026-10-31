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
from conftest import make_document, make_extract_response

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


def fresh_demo(demos_dir: Path, name: str) -> Path:
    """Return a demo project directory with no cache from earlier runs."""
    demo = demos_dir / name
    shutil.rmtree(demo / ".axbt", ignore_errors=True)
    return demo


class TestHelp:
    def test_help_lists_init_and_compile(self) -> None:
        result = runner.invoke(main, ["--help"])
        assert result.exit_code == 0
        assert "init" in result.output
        assert "compile" in result.output


class TestCompileDemos:
    def test_compile_creates_manifest_for_root_two_demo(
        self, demos_dir: Path, monkeypatch
    ) -> None:
        demo = fresh_demo(demos_dir, "RootTwoIrrational")
        assert not (demo / ".axbt").exists()
        monkeypatch.chdir(demo)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        assert manifest_path(demo).is_file()

    def test_demo_manifest_shape(self, demos_dir: Path, monkeypatch) -> None:
        demo = fresh_demo(demos_dir, "RootTwoIrrational")
        monkeypatch.chdir(demo)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        raw = json.loads(manifest_path(demo).read_text(encoding="utf-8"))
        assert set(raw) == {"version", "generated_at", "nodes"}
        assert raw["version"] == 2
        names = {node["name"] for node in raw["nodes"]}
        assert names == {
            "RootTwoIrrational.Divisibility",
            "RootTwoIrrational.EuclidLemma",
            "RootTwoIrrational.IrrationalSqrtTwo",
        }
        # And it still loads through our own loader.
        assert len(load_manifest(demo).nodes) == 3

    def test_demo_dag_edges(self, demos_dir: Path, monkeypatch) -> None:
        demo = fresh_demo(demos_dir, "RootTwoIrrational")
        monkeypatch.chdir(demo)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        by_name = load_manifest(demo).by_name()
        divisibility = by_name["RootTwoIrrational.Divisibility"]
        euclid = by_name["RootTwoIrrational.EuclidLemma"]
        irrational = by_name["RootTwoIrrational.IrrationalSqrtTwo"]

        assert divisibility.parents == []
        assert euclid.parents == ["RootTwoIrrational.Divisibility"]
        assert irrational.parents == [
            "RootTwoIrrational.Divisibility",
            "RootTwoIrrational.EuclidLemma",
        ]
        # children are the inverse of parents
        assert divisibility.children == [
            "RootTwoIrrational.EuclidLemma",
            "RootTwoIrrational.IrrationalSqrtTwo",
        ]
        assert irrational.children == []

    def test_demo_md5_fingerprints(self, demos_dir: Path, monkeypatch) -> None:
        demo = fresh_demo(demos_dir, "RootTwoIrrational")
        monkeypatch.chdir(demo)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        for node in load_manifest(demo).nodes:
            data = (demo / node.path).read_bytes()
            assert node.md5 == hashlib.md5(data).hexdigest()

    def test_compile_gauss_demo_via_default_dir(self, demos_dir: Path, monkeypatch) -> None:
        demo = fresh_demo(demos_dir, "GaussIntSum")
        monkeypatch.chdir(demo)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        manifest = load_manifest(demo)
        assert [node.name for node in manifest.nodes] == ["GaussIntSum.GaussSum"]
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


class TestExtraction:
    """Scope B: compile enriches the manifest with Axle-extracted
    declaration metadata, incrementally."""

    DEMO_DOCS = {
        "theorem prime_gt_one": {
            "prime_gt_one": make_document(
                "prime_gt_one",
                line_pos=11,
                end_line_pos=12,
                signature="theorem prime_gt_one (p : ℕ) (hp : Nat.Prime p) : 1 < p",
            ),
            "prime_dvd_square": make_document("prime_dvd_square", line_pos=15, end_line_pos=16),
        },
        "theorem euclid_lemma": {
            # Zero-based payload coordinates: the Euclid section starts at
            # one-based payload line 19 (after the hoisted import header and
            # the inlined Divisibility source), so the theorem at file line
            # 12 sits at zero-based payload line 27.
            "euclid_lemma": make_document("euclid_lemma", line_pos=27, end_line_pos=28),
        },
        "theorem sqrt_two_irrational": {
            # Zero-based payload line 42 == file line 15 (three imports
            # stripped, section starting at one-based payload line 32).
            "sqrt_two_irrational": make_document("sqrt_two_irrational", line_pos=42, end_line_pos=55),
        },
    }

    def test_demo_nodes_get_declaration_metadata(
        self, demos_dir: Path, fake_axle, monkeypatch
    ) -> None:
        from conftest import DEMO_EXTRACTION_DOCS

        fake_axle._extract_documents_by_marker = DEMO_EXTRACTION_DOCS
        demo = fresh_demo(demos_dir, "RootTwoIrrational")
        monkeypatch.chdir(demo)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        manifest = load_manifest(demo)
        divisibility = manifest.by_name()["RootTwoIrrational.Divisibility"]
        assert [d.name for d in divisibility.declarations] == [
            "prime_gt_one",
            "prime_dvd_square",
        ]
        assert divisibility.declarations[0].kind == "theorem"
        assert divisibility.declarations[0].is_sorry is False
        assert divisibility.declarations[0].line_pos == 11
        assert divisibility.declarations[0].end_line_pos == 12
        assert divisibility.declarations[0].signature.startswith("theorem prime_gt_one")
        euclid = manifest.by_name()["RootTwoIrrational.EuclidLemma"]
        assert [d.name for d in euclid.declarations] == ["euclid_lemma"]
        # EuclidLemma.lean has one intra-project import stripped from its
        # payload; the recorded position is shifted back into file coordinates.
        assert euclid.declarations[0].line_pos == 12
        irrational = manifest.by_name()["RootTwoIrrational.IrrationalSqrtTwo"]
        assert [d.name for d in irrational.declarations] == ["sqrt_two_irrational"]
        assert irrational.declarations[0].line_pos == 15

    def test_sorry_flag_is_recorded(self, make_project, tmp_path: Path, monkeypatch, fake_axle) -> None:
        from conftest import make_extract_response

        fake_axle._extract_documents = {
            "open_problem": make_document("open_problem", is_sorry=True, line_pos=0, end_line_pos=0)
        }
        root = make_project(tmp_path, SIMPLE_CONFIG, {"M/A.lean": "theorem open_problem : P := by sorry\n"})
        monkeypatch.chdir(root)

        assert runner.invoke(main, ["compile"]).exit_code == 0

        (node,) = load_manifest(root).nodes
        assert node.declarations[0].is_sorry is True

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
        self, demos_dir: Path, fake_axle, monkeypatch
    ) -> None:
        """Each node's manifest entry carries the request id of the API call
        that produced its data; carried-over nodes keep their original id."""
        demo = fresh_demo(demos_dir, "RootTwoIrrational")
        monkeypatch.chdir(demo)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        first = load_manifest(demo)
        assert all(node.request_id is not None for node in first.nodes)
        assert len({node.request_id for node in first.nodes}) == 3  # distinct calls
        assert set(first_node_ids := {node.request_id for node in first.nodes}) == set(
            fake_axle.request_ids
        )

        # A recompile carries the same provenance (no new requests).
        assert runner.invoke(main, ["compile"]).exit_code == 0
        assert load_manifest(demo).nodes[0].request_id in first_node_ids

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
        self, demos_dir: Path, fake_axle, monkeypatch
    ) -> None:
        demo = fresh_demo(demos_dir, "RootTwoIrrational")
        monkeypatch.chdir(demo)

        result = runner.invoke(main, ["compile"])

        assert result.exit_code == 0, result.output
        compiled = demo / ".axbt" / "compiled"
        assert sorted(p.name for p in compiled.iterdir()) == [
            "RootTwoIrrational_Divisibility_isolated.lean",
            "RootTwoIrrational_EuclidLemma_isolated.lean",
            "RootTwoIrrational_IrrationalSqrtTwo_isolated.lean",
        ]

        euclid_payload = (compiled / "RootTwoIrrational_EuclidLemma_isolated.lean").read_text(
            encoding="utf-8"
        )
        # Dependencies are inlined before the target file...
        assert euclid_payload.index("theorem prime_gt_one") < euclid_payload.index(
            "theorem euclid_lemma"
        )
        # ...intra-project imports are replaced by the inlined content...
        assert "import Divisibility" not in euclid_payload
        # ...and external imports are hoisted to the top exactly once.
        assert euclid_payload.count("import Mathlib") == 1
        assert euclid_payload.splitlines()[0] == "import Mathlib"

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
