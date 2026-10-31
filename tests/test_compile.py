"""CLI-level tests for `axbt compile`, driven through the real entry point."""

from __future__ import annotations

import hashlib
import json
import shutil
from pathlib import Path

from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.manifest import (
    MANIFEST_FILENAME,
    load_manifest,
    manifest_path,
)

runner = CliRunner()

SIMPLE_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""


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
        assert raw["version"] == 1
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
