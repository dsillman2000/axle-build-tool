"""Unit tests for `--select` resolution and selection payload assembly."""

from __future__ import annotations

from pathlib import Path

import pytest

from axle_build_tool.config import load_config
from axle_build_tool.manifest import build_manifest
from axle_build_tool.payloads import build_payload, compiled_filename
from axle_build_tool.selection import Selection, SelectionError, resolve_selection

SIMPLE_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""


@pytest.fixture
def demo_state(demos_dir: Path):
    """The RootTwoIrrational demo with representative extraction data stamped in."""
    from conftest import with_declarations

    root = demos_dir / "RootTwoIrrational"
    config = load_config(root)
    manifest = build_manifest(root, config, None)
    manifest = with_declarations(
        manifest,
        {
            "RootTwoIrrational.Divisibility": ["prime_gt_one", "prime_dvd_square"],
            "RootTwoIrrational.EuclidLemma": ["euclid_lemma"],
            "RootTwoIrrational.IrrationalSqrtTwo": ["sqrt_two_irrational"],
        },
    )
    return config, manifest, root


class TestResolveSelection:
    def test_module_selection(self, demo_state) -> None:
        config, manifest, _ = demo_state
        selection = resolve_selection("RootTwoIrrational", config, manifest)
        assert selection == Selection(module="RootTwoIrrational")
        assert selection.node_name is None
        assert selection.declaration is None

    def test_file_selection(self, demo_state) -> None:
        config, manifest, _ = demo_state
        selection = resolve_selection("RootTwoIrrational.Divisibility", config, manifest)
        assert selection == Selection(
            module="RootTwoIrrational", node_name="RootTwoIrrational.Divisibility"
        )

    def test_declaration_selection(self, demo_state) -> None:
        config, manifest, _ = demo_state
        selection = resolve_selection(
            "RootTwoIrrational.EuclidLemma.euclid_lemma", config, manifest
        )
        assert selection == Selection(
            module="RootTwoIrrational",
            node_name="RootTwoIrrational.EuclidLemma",
            declaration="euclid_lemma",
        )

    def test_dotted_lean_declaration_names_resolve_greedily(
        self, make_project, tmp_path: Path
    ) -> None:
        root = make_project(
            tmp_path,
            SIMPLE_CONFIG,
            {
                "M/A.lean": "theorem A.t : True := True.intro\n",
                "M/Utils/Basic.lean": "def Utils.Basic.x := 1\n",
            },
        )
        config = load_config(root)
        from conftest import with_declarations

        manifest = with_declarations(
            build_manifest(root, config, None),
            {"M.A": ["A.t"], "M.Utils.Basic": ["Utils.Basic.x"]},
        )

        # Greedy: the stem `Utils.Basic` matches, and the remainder `x`
        # resolves by unique suffix to the declaration `Utils.Basic.x`.
        selection = resolve_selection("M.Utils.Basic.x", config, manifest)
        assert selection.node_name == "M.Utils.Basic"
        assert selection.declaration == "Utils.Basic.x"

        # The plain stem still resolves, with the rest as the declaration.
        selection = resolve_selection("M.A.t", config, manifest)
        assert selection.node_name == "M.A"
        # The stored declaration is the full extracted name.
        assert selection.declaration == "A.t"

    def test_unknown_module_names_valid_modules(self, demo_state) -> None:
        config, manifest, _ = demo_state
        with pytest.raises(SelectionError, match=r"Unknown module 'Nope'.*RootTwoIrrational"):
            resolve_selection("Nope.Divisibility", config, manifest)

    def test_unknown_stem_lists_available_stems(self, demo_state) -> None:
        config, manifest, _ = demo_state
        with pytest.raises(SelectionError, match=r"no file stem matches 'Nope'.*Divisibility"):
            resolve_selection("RootTwoIrrational.Nope", config, manifest)

    def test_unknown_declaration_lists_extracted_declarations(
        self, demo_state
    ) -> None:
        config, manifest, _ = demo_state
        with pytest.raises(SelectionError, match=r"'nope' not found.*prime_gt_one"):
            resolve_selection("RootTwoIrrational.Divisibility.nope", config, manifest)

    def test_unknown_nested_stem_is_rejected(self, demo_state) -> None:
        config, manifest, _ = demo_state
        # The stem `Divisibility` matches, so the remainder is diagnosed as
        # an unknown declaration rather than an unknown stem.
        with pytest.raises(SelectionError, match=r"declaration 'Nope\.thing' not found"):
            resolve_selection("RootTwoIrrational.Divisibility.Nope.thing", config, manifest)

    def test_empty_module_selection_is_rejected(self, make_project, tmp_path: Path) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, files={})
        (root / "M").mkdir()
        config = load_config(root)
        manifest = build_manifest(root, config, None)

        with pytest.raises(SelectionError, match="has no .lean files"):
            resolve_selection("M", config, manifest)


class TestSelectionPayloads:
    def test_module_selection_covers_all_files_in_dependency_order(
        self, demo_state
    ) -> None:
        config, manifest, root = demo_state
        selection = resolve_selection("RootTwoIrrational", config, manifest)

        payload = build_payload(selection.payload_nodes(manifest), manifest, root)

        assert list(payload.sections) == [
            "RootTwoIrrational.Divisibility",
            "RootTwoIrrational.EuclidLemma",
            "RootTwoIrrational.IrrationalSqrtTwo",
        ]
        # Dependencies first: Divisibility's source appears before Euclid's.
        assert payload.content.index("theorem prime_gt_one") < payload.content.index(
            "theorem euclid_lemma"
        )
        assert "theorem sqrt_two_irrational" in payload.content

    def test_declaration_selection_payload_equals_file_payload(
        self, demo_state
    ) -> None:
        config, manifest, root = demo_state
        file_selection = resolve_selection("RootTwoIrrational.EuclidLemma", config, manifest)
        decl_selection = resolve_selection(
            "RootTwoIrrational.EuclidLemma.euclid_lemma", config, manifest
        )

        file_payload = build_payload(file_selection.payload_nodes(manifest), manifest, root)
        decl_payload = build_payload(decl_selection.payload_nodes(manifest), manifest, root)

        assert decl_payload.content == file_payload.content

    def test_module_selection_inlines_cross_module_dependencies(
        self, make_project, tmp_path: Path
    ) -> None:
        root = make_project(
            tmp_path,
            "modules:\n  M:\n    targets: []\n  N:\n    targets: []\n",
            {
                "N/A.lean": "def shared := 1\n",
                "M/B.lean": "import A\ndef uses_it := shared\n",
            },
        )
        config = load_config(root)
        manifest = build_manifest(root, config, None)
        selection = resolve_selection("M", config, manifest)

        payload = build_payload(selection.payload_nodes(manifest), manifest, root)

        # N's A.lean is a dependency of M/B.lean and is inlined first.
        assert list(payload.sections) == ["N.A", "M.B"]
        assert payload.content.index("def shared") < payload.content.index("def uses_it")

    def test_compiled_filename_mapping(self) -> None:
        assert compiled_filename("M") == "M_isolated.lean"
        assert compiled_filename("M", "A") == "M_A_isolated.lean"
        assert compiled_filename("M", "Utils.Basic") == "M_Utils_Basic_isolated.lean"

    def test_selection_compiled_filename(self, demo_state) -> None:
        config, manifest, _ = demo_state
        assert (
            resolve_selection("RootTwoIrrational", config, manifest).compiled_filename
            == "RootTwoIrrational_isolated.lean"
        )
        assert (
            resolve_selection("RootTwoIrrational.Divisibility", config, manifest).compiled_filename
            == "RootTwoIrrational_Divisibility_isolated.lean"
        )
        assert (
            resolve_selection(
                "RootTwoIrrational.Divisibility.prime_gt_one", config, manifest
            ).compiled_filename
            == "RootTwoIrrational_Divisibility_isolated.lean"
        )
