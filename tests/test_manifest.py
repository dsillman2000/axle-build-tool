"""Unit tests for the DAG builder and manifest persistence."""

from __future__ import annotations

import hashlib
from datetime import datetime, timezone
from pathlib import Path

import pytest

from axle_build_tool.config import ProjectConfig, load_config
from axle_build_tool.manifest import (
    Manifest,
    ManifestError,
    ManifestNode,
    ExtractedDecl,
    build_manifest,
    check_targets,
    load_manifest,
    manifest_path,
    save_manifest,
)

SIMPLE_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""


@pytest.fixture
def simple_project(make_project, tmp_path: Path) -> Path:
    """A two-file project: M/A.lean with no imports, M/B.lean importing A."""
    return make_project(
        tmp_path,
        SIMPLE_CONFIG,
        {
            "M/A.lean": "def x := 1\n",
            "M/B.lean": "import A\ndef y := x\n",
        },
    )


def config_of(root: Path):
    return load_config(root)


class TestBuildManifest:
    def test_md5_matches_file_contents(self, simple_project: Path) -> None:
        config = config_of(simple_project)
        manifest = build_manifest(simple_project, config)

        for node in manifest.nodes:
            data = (simple_project / node.path).read_bytes()
            assert node.md5 == hashlib.md5(data).hexdigest()

    def test_dag_edges_and_inverse_children(self, simple_project: Path) -> None:
        config = config_of(simple_project)
        manifest = build_manifest(simple_project, config)
        by_name = manifest.by_name()

        assert by_name["M.A"].parents == []
        assert by_name["M.A"].children == ["M.B"]
        assert by_name["M.B"].parents == ["M.A"]

    def test_external_imports_are_ignored(self, make_project, tmp_path: Path) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {"M/A.lean": "import Init\nimport Init.System.IO\ndef x := 1\n"},
        )
        config = config_of(root)
        manifest = build_manifest(root, config)

        assert [node.name for node in manifest.nodes] == ["M.A"]
        assert manifest.nodes[0].parents == []
        assert manifest.nodes[0].imports == ["Init", "Init.System.IO"]

    def test_nested_file_stems_are_dotted(self, make_project, tmp_path: Path) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {
                "M/Utils/Basic.lean": "def base := 1\n",
                "M/Main.lean": "import Utils.Basic\ndef top := base\n",
            },
        )
        config = config_of(root)
        manifest = build_manifest(root, config)

        by_name = manifest.by_name()
        assert set(by_name) == {"M.Utils.Basic", "M.Main"}
        assert by_name["M.Main"].parents == ["M.Utils.Basic"]

    def test_import_cycle_is_rejected(self, make_project, tmp_path: Path) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {
                "M/A.lean": "import B\ndef x := 1\n",
                "M/B.lean": "import A\ndef y := 1\n",
            },
        )
        with pytest.raises(ManifestError, match=r"[Cc]ycle.*M\.A.*M\.B"):
            build_manifest(root, config_of(root))

    def test_self_import_is_rejected(self, make_project, tmp_path: Path) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, {"M/A.lean": "import A\n"})
        with pytest.raises(ManifestError, match=r"[Cc]ycle"):
            build_manifest(root, config_of(root))

    def test_ambiguous_import_names_candidates(self, make_project, tmp_path: Path) -> None:
        root = make_project(
            tmp_path,
            "modules:\n  M:\n    targets: []\n  N:\n    targets: []\n  P:\n    targets: []\n",
            {
                "M/A.lean": "def m := 1\n",
                "N/A.lean": "def n := 1\n",
                "P/B.lean": "import A\ndef b := 1\n",
            },
        )
        with pytest.raises(ManifestError, match=r"ambiguous.*M\.A.*N\.A"):
            build_manifest(root, config_of(root))

    def test_same_module_wins_over_project_wide_match(
        self, make_project, tmp_path: Path
    ) -> None:
        root = make_project(
            tmp_path,
            "modules:\n  M:\n    targets: []\n  N:\n    targets: []\n",
            {
                "M/A.lean": "def m := 1\n",
                "N/A.lean": "def n := 1\n",
                "M/B.lean": "import A\ndef b := m\n",
            },
        )
        manifest = build_manifest(root, config_of(root))
        # `import A` from M/B must resolve within M, not N.
        assert manifest.by_name()["M.B"].parents == ["M.A"]


class TestStatusTracking:
    def test_first_run_marks_all_nodes_new(self, simple_project: Path) -> None:
        manifest = build_manifest(simple_project, config_of(simple_project))
        assert {node.status for node in manifest.nodes} == {"new"}

    def test_unchanged_sources_are_clean(self, simple_project: Path) -> None:
        config = config_of(simple_project)
        first = build_manifest(simple_project, config)
        second = build_manifest(simple_project, config, previous=first)

        assert {node.status for node in second.nodes} == {"clean"}
        assert [
            (n.name, n.md5, tuple(n.parents), tuple(n.children)) for n in first.nodes
        ] == [(n.name, n.md5, tuple(n.parents), tuple(n.children)) for n in second.nodes]

    def test_edited_source_is_changed(self, simple_project: Path) -> None:
        config = config_of(simple_project)
        first = build_manifest(simple_project, config)
        (simple_project / "M/A.lean").write_text("def x := 2\n", encoding="utf-8")

        second = build_manifest(simple_project, config, previous=first)

        assert second.by_name()["M.A"].status == "changed"
        assert second.by_name()["M.B"].status == "clean"

    def _with_extracted_data(self, manifest: Manifest) -> Manifest:
        declaration = ExtractedDecl(
            name="sample_decl",
            kind="theorem",
            is_sorry=False,
            line_pos=1,
            end_line_pos=2,
            signature="theorem sample_decl : True",
        )
        return manifest.model_copy(
            update={
                "nodes": [
                    node.model_copy(
                        update={
                            "extraction": "ok",
                            "declarations": [declaration],
                        }
                    )
                    for node in manifest.nodes
                ]
            }
        )

    def test_unchanged_nodes_carry_extraction_data(self, simple_project: Path) -> None:
        config = config_of(simple_project)
        first = self._with_extracted_data(build_manifest(simple_project, config))

        second = build_manifest(simple_project, config, previous=first)

        for node in second.nodes:
            assert node.extraction == "ok"
            assert [d.name for d in node.declarations] == ["sample_decl"]

    def test_changed_nodes_drop_stale_extraction_data(self, simple_project: Path) -> None:
        config = config_of(simple_project)
        first = self._with_extracted_data(build_manifest(simple_project, config))
        (simple_project / "M/A.lean").write_text("def x := 2\n", encoding="utf-8")

        second = build_manifest(simple_project, config, previous=first)

        changed = second.by_name()["M.A"]
        assert changed.status == "changed"
        assert changed.extraction is None  # pending: re-extracted by the command
        assert changed.declarations == []
        carried = second.by_name()["M.B"]
        assert carried.extraction == "ok"
        assert [d.name for d in carried.declarations] == ["sample_decl"]

    def test_pre_v2_manifest_nodes_are_pending_extraction(self, simple_project: Path) -> None:
        config = config_of(simple_project)
        first = build_manifest(simple_project, config)

        # Simulate a v1 manifest: nodes carry no extraction fields at all.
        stripped_previous = Manifest.model_validate(
            {
                "version": 1,
                "generated_at": first.generated_at.isoformat(),
                "nodes": [
                    {
                        key: value
                        for key, value in node.model_dump(mode="json").items()
                        if key not in ("extraction", "declarations")
                    }
                    for node in first.nodes
                ],
            }
        )

        second = build_manifest(simple_project, config, previous=stripped_previous)

        assert all(node.extraction is None for node in second.nodes)
        assert all(node.declarations == [] for node in second.nodes)


class TestPersistence:
    def test_save_and_load_round_trip(self, simple_project: Path) -> None:
        manifest = build_manifest(simple_project, config_of(simple_project))
        save_manifest(manifest, simple_project)

        loaded = load_manifest(simple_project)
        assert loaded == manifest

    def test_load_missing_manifest_raises(self, simple_project: Path) -> None:
        with pytest.raises(ManifestError, match="manifest.json"):
            load_manifest(simple_project)

    def test_load_invalid_manifest_raises(self, simple_project: Path) -> None:
        save_manifest(build_manifest(simple_project, config_of(simple_project)), simple_project)
        path = manifest_path(simple_project)
        path.write_text('{"version": 99}', encoding="utf-8")

        with pytest.raises(ManifestError, match="[Ii]nvalid"):
            load_manifest(simple_project)

    def test_save_creates_the_cache_directory(self, simple_project: Path) -> None:
        assert not (simple_project / ".axbt").exists()
        save_manifest(build_manifest(simple_project, config_of(simple_project)), simple_project)
        assert manifest_path(simple_project).is_file()


class TestTargetValidation:
    def _config_with_target(self, target: str):
        from axle_build_tool.config import ModuleConfig

        return ProjectConfig(
            name="proj",
            modules={"M": ModuleConfig(name="M", dir="M", targets=(target,))},
        )

    def _one_node_manifest(self) -> Manifest:
        return Manifest(
            generated_at=datetime.now(timezone.utc),
            nodes=[ManifestNode(
                name="M.A", module="M", path="M/A.lean",
                md5="0" * 32, status="new",
            )],
        )

    def test_dangling_target_is_rejected(self) -> None:
        config = self._config_with_target("Missing.thm")
        with pytest.raises(ManifestError, match=r"'Missing\.thm'"):
            check_targets(config, self._one_node_manifest())

    def test_valid_target_stem_passes(self) -> None:
        config = self._config_with_target("A.some_decl")
        check_targets(config, self._one_node_manifest())  # should not raise

    def test_nested_target_stem_matches_greedily(self) -> None:
        config = self._config_with_target("Utils.Basic.thm")
        manifest = Manifest(
            generated_at=datetime.now(timezone.utc),
            nodes=[ManifestNode(
                name="M.Utils.Basic", module="M", path="M/Utils/Basic.lean",
                md5="0" * 32, status="new",
            )],
        )
        check_targets(config, manifest)  # should not raise
