"""Unit tests for `--select` resolution and selection payload assembly."""

from __future__ import annotations

from pathlib import Path

import pytest

from axle_build_tool.config import load_config
from axle_build_tool.manifest import build_manifest
from axle_build_tool.payloads import (
    build_payload,
    compiled_filename,
    source_position,
)
from axle_build_tool.selection import Selection, SelectionError, resolve_selection

SIMPLE_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""

# A synthetic dependency-chain project with the shapes the demo projects
# used to provide to the offline suite: a hoisted external import, a
# module-docstring shift, an A <- B <- C chain, and a nested file stem.
CHAIN_FILES = {
    "M/A.lean": "import Mathlib\n\n/-! Base definitions. -/\n\ndef base := 1\n",
    "M/B.lean": "import A\ndef middle := base + 1\n",
    "M/C.lean": "import B\ntheorem top : middle = 2 := by decide\n",
    "M/Utils/Basic.lean": "def Utils.Basic.x := 1\n",
}

CHAIN_DECLARATIONS = {
    "M.A": ["base"],
    "M.B": ["middle"],
    "M.C": ["top"],
    "M.Utils.Basic": ["Utils.Basic.x"],
}


@pytest.fixture
def chain_state(make_project, tmp_path: Path):
    """The chain project with representative extraction data stamped in."""
    from conftest import with_declarations

    root = make_project(tmp_path, SIMPLE_CONFIG, CHAIN_FILES)
    config = load_config(root)
    manifest = with_declarations(build_manifest(root, config, None), CHAIN_DECLARATIONS)
    return config, manifest, root


RAGGED_CONFIG = """\
project:
  name: ragged
modules:
  M:
    targets: []
  N:
    targets: []
"""

# A project with comment/blank-line noise around real code: a hoisted
# external import, a `/-!` section header, a preserved docstring, an
# inline line comment, and a full-line comment.
RAGGED_FILES = {
    "N/base.lean": (
        "import Mathlib\n"                             # 1
        "\n"                                            # 2
        "/-! Base definitions. -/\n"                    # 3
        "\n"                                            # 4
        "/-- The shared base. -/\n"                     # 5
        "def base := 1\n"                               # 6
        "\n"                                            # 7
        "def extra := base -- note\n"                   # 8
    ),
    "N/bad.lean": '-- build-up comment\ntheorem ugly := "unterminated\n',
    "M/uses.lean": (
        "import base\n"                                 # 1
        "-- what follows\n"                             # 2
        "theorem top : base = 1 := rfl\n"               # 3
    ),
}


class TestMinifiedPayload:
    """Payload minification at assembly: comments and blank lines are
    dropped while the line maps keep pointing at original source lines."""

    @pytest.fixture
    def ragged(self, make_project, tmp_path: Path):
        root = make_project(tmp_path, RAGGED_CONFIG, RAGGED_FILES)
        config = load_config(root)
        manifest = build_manifest(root, config, None)
        return config, manifest, root

    def test_comments_and_blank_lines_are_dropped_docstrings_survive(
        self, ragged
    ) -> None:
        _config, manifest, root = ragged
        selection_nodes = [manifest.by_name()["M.uses"]]
        payload = build_payload(selection_nodes, manifest, root, minify=True)

        assert "-- what follows" not in payload.content
        start, end = payload.sections["N.base"]
        section_lines = payload.lines[start - 1 : end]
        # Only non-blank, comment-free code lines survive the section.
        assert all(line.strip() for line in section_lines)
        assert not any(line.lstrip().startswith("--") for line in section_lines)
        assert "/-! Base definitions. -/" not in payload.content
        assert "/-- The shared base. -/" in payload.content

    def test_line_maps_track_surviving_source_lines(self, ragged) -> None:
        _config, manifest, root = ragged
        payload = build_payload(
            [manifest.by_name()["M.uses"]], manifest, root, minify=True
        )

        # N.base: the hoisted import, blank lines, and the `/-!` header go;
        # docstring, defs (one with `-- note` stripped), keep their numbers.
        assert payload.line_map["N.base"] == [5, 6, 8]
        # M.uses: the full-line comment (source line 2) is dropped.
        assert payload.line_map["M.uses"] == [3]
        start, _end = payload.sections["N.base"]
        assert source_position(payload, start + 1) == ("N.base", 6)
        uses_start, uses_end = payload.sections["M.uses"]
        assert source_position(payload, uses_start) == ("M.uses", 3)

    def test_minified_content_matches_all_responses(self, ragged) -> None:
        _config, manifest, root = ragged

        payload = build_payload(
            [manifest.by_name()["M.uses"]], manifest, root, minify=True
        )
        # The section text itself survives; only layout does not.
        assert "def base := 1" in payload.content
        assert "def extra := base" in payload.content
        assert "theorem top : base = 1 := rfl" in payload.content

    def test_default_payloads_stay_raw(self, ragged) -> None:
        """Extraction payloads and default `build_payload` calls keep the
        raw text (manifest spans are keyed to unminified source)."""
        _config, manifest, root = ragged
        payload = build_payload([manifest.by_name()["M.uses"]], manifest, root)

        assert "-- what follows" in payload.content
        assert payload.line_map["M.uses"] == [2, 3]

    def test_untrackable_files_are_submitted_unminified(self, ragged) -> None:
        """A file that doesn't track (unterminated string) falls back to
        raw, comment lines and all."""
        _config, manifest, root = ragged
        payload = build_payload(
            [manifest.by_name()["N.bad"]], manifest, root, minify=True
        )

        assert "-- build-up comment" in payload.content
        start, _end = payload.sections["N.bad"]
        section = payload.lines[start - 1 : _end]
        assert section[0] == "-- build-up comment"
    def test_module_selection(self, chain_state) -> None:
        config, manifest, _ = chain_state
        selection = resolve_selection("M", config, manifest)
        assert selection == Selection(module="M")
        assert selection.node_name is None
        assert selection.declaration is None

    def test_file_selection(self, chain_state) -> None:
        config, manifest, _ = chain_state
        selection = resolve_selection("M.B", config, manifest)
        assert selection == Selection(module="M", node_name="M.B")

    def test_declaration_selection(self, chain_state) -> None:
        config, manifest, _ = chain_state
        selection = resolve_selection("M.C.top", config, manifest)
        assert selection == Selection(
            module="M", node_name="M.C", declaration="top"
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

    def test_unknown_module_names_valid_modules(self, chain_state) -> None:
        config, manifest, _ = chain_state
        with pytest.raises(SelectionError, match=r"Unknown module 'Nope'.*yml: M\."):
            resolve_selection("Nope.Divisibility", config, manifest)

    def test_unknown_stem_lists_available_stems(self, chain_state) -> None:
        config, manifest, _ = chain_state
        with pytest.raises(
            SelectionError, match=r"no file stem matches 'Nope'.*A, B, C, Utils\.Basic"
        ):
            resolve_selection("M.Nope", config, manifest)

    def test_unknown_declaration_lists_extracted_declarations(
        self, chain_state
    ) -> None:
        config, manifest, _ = chain_state
        with pytest.raises(SelectionError, match=r"'nope' not found.*\btop\b"):
            resolve_selection("M.C.nope", config, manifest)

    def test_unknown_nested_stem_is_rejected(self, chain_state) -> None:
        config, manifest, _ = chain_state
        # The stem `C` matches, so the remainder is diagnosed as
        # an unknown declaration rather than an unknown stem.
        with pytest.raises(SelectionError, match=r"declaration 'Nope\.thing' not found"):
            resolve_selection("M.C.Nope.thing", config, manifest)

    def test_empty_module_selection_is_rejected(self, make_project, tmp_path: Path) -> None:
        root = make_project(tmp_path, SIMPLE_CONFIG, files={})
        (root / "M").mkdir()
        config = load_config(root)
        manifest = build_manifest(root, config, None)

        with pytest.raises(SelectionError, match="has no .lean files"):
            resolve_selection("M", config, manifest)


class TestReadOnlyAgainstRicherRecords:
    """Selection resolution reads declaration *names* only: dependency
    lists and the checked/verified stamp tiers must not affect it."""

    def test_resolution_is_unchanged_by_the_outcome_fields(self, chain_state) -> None:
        from datetime import datetime, timezone

        config, manifest, _ = chain_state
        stamped = manifest.model_copy(
            update={
                "nodes": [
                    node.model_copy(
                        update={
                            "declarations": [
                                declaration.model_copy(
                                    update={
                                        "dependencies": ["external.things"],
                                        "external_dependencies": ["Nat"],
                                        "checked_sig": "c" * 32,
                                        "checked_at": datetime.now(timezone.utc),
                                        "checked_request_id": "req-check",
                                        "verified_sig": "v" * 32,
                                        "verified_at": datetime.now(timezone.utc),
                                        "verified_request_id": "req-verify",
                                    }
                                )
                                for declaration in node.declarations
                            ]
                        }
                    )
                    for node in manifest.nodes
                ]
            }
        )

        for selector, _expected in (
            ("M", None),
            ("M.B", None),
            ("M.C", None),
            ("M.C.top", None),
            ("M.Utils.Basic.x", None),
        ):
            assert resolve_selection(selector, config, manifest) == resolve_selection(
                selector, config, stamped
            )


class TestSelectionPayloads:
    def test_module_selection_covers_all_files_in_dependency_order(
        self, chain_state
    ) -> None:
        config, manifest, root = chain_state
        selection = resolve_selection("M", config, manifest)

        payload = build_payload(selection.payload_nodes(manifest), manifest, root)

        assert list(payload.sections) == ["M.A", "M.B", "M.C", "M.Utils.Basic"]
        # Dependencies first: A's source appears before B's, B's before C's.
        assert payload.content.index("def base") < payload.content.index(
            "def middle"
        ) < payload.content.index("theorem top")
        assert "def Utils.Basic.x" in payload.content

    def test_declaration_selection_payload_equals_file_payload(
        self, chain_state
    ) -> None:
        config, manifest, root = chain_state
        file_selection = resolve_selection("M.C", config, manifest)
        decl_selection = resolve_selection("M.C.top", config, manifest)

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

    def test_selection_compiled_filename(self, chain_state) -> None:
        config, manifest, _ = chain_state
        assert (
            resolve_selection("M", config, manifest).compiled_filename
            == "M_isolated.lean"
        )
        assert (
            resolve_selection("M.C", config, manifest).compiled_filename
            == "M_C_isolated.lean"
        )
        assert (
            resolve_selection("M.C.top", config, manifest).compiled_filename
            == "M_C_isolated.lean"
        )

    def test_line_map_attributes_section_lines_to_source_lines(
        self, chain_state
    ) -> None:
        config, manifest, root = chain_state
        selection = resolve_selection("M.A", config, manifest)

        payload = build_payload(selection.payload_nodes(manifest), manifest, root)

        start, end = payload.sections["M.A"]
        mapped = payload.line_map["M.A"]
        assert len(mapped) == end - start + 1
        # The mapping is exact: the section's last line is the file's
        # last line, and positions strictly increase (import lines were
        # skipped, not shifted over).
        source_lines = (root / "M/A.lean").read_text(encoding="utf-8").splitlines()
        assert mapped[-1] == len(source_lines)
        assert all(before < after for before, after in zip(mapped, mapped[1:]))
        # The hoisted import header has no source counterpart.
        assert source_position(payload, start - 1) is None
        assert source_position(payload, start) == ("M.A", mapped[0])
