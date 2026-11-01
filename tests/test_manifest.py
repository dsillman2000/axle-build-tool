"""Unit tests for the DAG builder and manifest persistence."""

from __future__ import annotations

import hashlib
from datetime import datetime, timezone
from pathlib import Path

import pytest

from axle_build_tool.config import ProjectConfig, load_config
from axle_build_tool.manifest import (
    MANIFEST_VERSION,
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
                    node.model_copy(update={"declarations": [declaration]})
                    for node in manifest.nodes
                ]
            }
        )

    def test_unchanged_nodes_carry_extraction_data(self, simple_project: Path) -> None:
        config = config_of(simple_project)
        first = self._with_extracted_data(build_manifest(simple_project, config))

        second = build_manifest(simple_project, config, previous=first)

        for node in second.nodes:
            assert [d.name for d in node.declarations] == ["sample_decl"]

    def test_request_id_provenance_is_carried_with_data(self, simple_project: Path) -> None:
        config = config_of(simple_project)
        first = build_manifest(simple_project, config)
        stamped = first.model_copy(
            update={
                "nodes": [
                    node.model_copy(update={"request_id": f"req-{node.name}"})
                    for node in first.nodes
                ]
            }
        )

        second = build_manifest(simple_project, config, previous=stamped)

        for node in second.nodes:
            # Carried data keeps the request that produced it.
            assert node.request_id == f"req-{node.name}"

    def test_changed_nodes_drop_stale_extraction_data(self, simple_project: Path) -> None:
        config = config_of(simple_project)
        first = self._with_extracted_data(build_manifest(simple_project, config))
        (simple_project / "M/A.lean").write_text("def x := 2\n", encoding="utf-8")

        second = build_manifest(simple_project, config, previous=first)

        changed = second.by_name()["M.A"]
        assert changed.status == "changed"
        assert changed.declarations == []  # pending: re-extracted by the command
        assert changed.request_id is None  # fresh provenance after re-extraction
        carried = second.by_name()["M.B"]
        assert [d.name for d in carried.declarations] == ["sample_decl"]


class TestPersistence:
    def test_save_and_load_round_trip(self, simple_project: Path) -> None:
        manifest = build_manifest(simple_project, config_of(simple_project))
        save_manifest(manifest, simple_project)

        loaded = load_manifest(simple_project)
        assert loaded == manifest

    def test_extracted_decl_outcome_fields_round_trip(
        self, simple_project: Path
    ) -> None:
        """Dependency lists and both stamp tiers survive persistence
        (all additive optional fields on the v2 declaration model)."""
        manifest = build_manifest(simple_project, config_of(simple_project))
        declaration = ExtractedDecl(
            name="sample_decl",
            kind="theorem",
            is_sorry=False,
            line_pos=1,
            end_line_pos=2,
            signature="theorem sample_decl : True",
            dependencies=["x", "y"],
            external_dependencies=["Nat", "Eq"],
            checked_sig="abc123",
            checked_at=datetime(2026, 1, 1, tzinfo=timezone.utc),
            checked_request_id="req-check",
            verified_sig="def456",
            verified_at=datetime(2026, 1, 2, tzinfo=timezone.utc),
            verified_request_id="req-verify",
        )
        stamped = manifest.model_copy(
            update={
                "nodes": [
                    node.model_copy(update={"declarations": [declaration]})
                    for node in manifest.nodes
                ]
            }
        )
        save_manifest(stamped, simple_project)

        assert load_manifest(simple_project) == stamped

    def test_manifest_from_before_the_change_loads_with_defaults(
        self, simple_project: Path
    ) -> None:
        """The additive contract: manifest JSON written before the
        dependency and outcome fields existed — without those keys —
        validates with every one of them defaulted."""
        import json

        manifest = build_manifest(simple_project, config_of(simple_project))
        save_manifest(manifest, simple_project)
        raw = json.loads(manifest_path(simple_project).read_text(encoding="utf-8"))
        new_fields = (
            "dependencies",
            "external_dependencies",
            "checked_sig",
            "checked_at",
            "checked_request_id",
            "verified_sig",
            "verified_at",
            "verified_request_id",
        )
        for node in raw["nodes"]:
            for decl in node["declarations"]:
                for field in new_fields:
                    decl.pop(field, None)
        manifest_path(simple_project).write_text(
            json.dumps(raw, indent=2), encoding="utf-8"
        )

        reloaded = load_manifest(simple_project)
        assert reloaded.version == MANIFEST_VERSION
        for decl in (d for node in reloaded.nodes for d in node.declarations):
            assert decl.dependencies == []
            assert decl.external_dependencies == []
            for field in new_fields:
                if field in ("dependencies", "external_dependencies"):
                    continue
                assert getattr(decl, field) is None

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
