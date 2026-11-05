"""Unit tests for extraction — mapping API documents to file coordinates.

`_decl_from_document` maps each extracted document's payload coordinates
back into the declaration's file (through the payload line map), snapping
the reported start onto the declaration's keyword line so the recorded
span reliably points at the declaration. Modifier-prefixed heads
(`private theorem`, …) must snap to their own line, not to some later
raw-keyword declaration in the section.
"""

from __future__ import annotations

from axle_build_tool.extraction import _decl_from_document
from axle_build_tool.payloads import Payload
from conftest import make_document


def payload_with(lines: list[str], header_lines: int = 0) -> Payload:
    """A single-section payload whose line map points "file lines" at
    `41+i` — the de-inlined offsets make coordinate mix-ups loud."""
    return Payload(
        content="\n".join(lines),
        lines=lines,
        sections={"M.F": (header_lines + 1, len(lines))},
        line_map={
            "M.F": list(range(41 + header_lines, 41 + len(lines) + 1))
            + [None] * header_lines
        },
        kept={},
    )


def document_for(payload_line: int, end_line: int, kind: str = "theorem"):
    return make_document(
        name="shrink",
        kind=kind,
        line_pos=payload_line,
        end_line_pos=end_line,
        signature="theorem shrink : True",
    )


def test_modifier_prefixed_head_snaps_to_its_own_line() -> None:
    payload = payload_with(
        [
            "",                                   # p1 (header line, no import mapping)
            "private theorem shrink (n : Nat) : n = n := rfl",  # p2
            "theorem grow : True := trivial",     # p3
        ],
        header_lines=1,
    )
    # The API reports the declaration's start on the `private` line.
    doc = document_for(2, 2)

    declaration = _decl_from_document(doc, payload, "M.F")

    assert declaration is not None
    # Snapped to the `private theorem` line — NOT to the later raw
    # `theorem grow` line (the pre-#38 snap walked straight past it).
    assert declaration.line_pos == 42


def test_attribute_then_modifier_head_snaps_to_its_own_line() -> None:
    payload = payload_with(
        [
            "@[simp] private theorem shrink : True := trivial",  # p1
            "theorem grow : True := trivial",                    # p2
        ],
    )
    doc = document_for(1, 1)

    declaration = _decl_from_document(doc, payload, "M.F")

    assert declaration is not None
    assert declaration.line_pos == 41


def test_defining_variant_kinds_snap_to_their_own_line() -> None:
    payload = payload_with(
        [
            "noncomputable def shrink : Nat := 0",  # p1
            "theorem grow : True := trivial",       # p2
        ],
    )
    doc = document_for(1, 1, kind="def")

    declaration = _decl_from_document(doc, payload, "M.F")

    assert declaration is not None
    assert declaration.line_pos == 41


def test_multiline_docstring_start_snaps_to_the_keyword_line() -> None:
    payload = payload_with(
        [
            "/-- shrink's doc,",          # p1
            " spanning lines -/",         # p2
            "private theorem shrink : True := trivial",  # p3
            "theorem grow : True := trivial",            # p4
        ],
    )
    doc = document_for(1, 3)

    declaration = _decl_from_document(doc, payload, "M.F")

    assert declaration is not None
    assert declaration.line_pos == 43


def test_scan_overrun_at_the_section_end_keeps_the_reported_start() -> None:
    payload = payload_with(
        [
            "private theorem shrink : True := trivial",  # p1
            "",                                          # p2 (section end)
        ],
    )
    doc = document_for(1, 1)

    declaration = _decl_from_document(doc, payload, "M.F")

    assert declaration is not None
    assert declaration.line_pos == 41


def test_end_out_of_section_keeps_the_declaration_length() -> None:
    payload = payload_with(
        [
            "private theorem shrink : True := trivial",  # p1
        ],
    )
    # The API reported an end beyond the section (a corrupt document).
    doc = document_for(1, 5)

    declaration = _decl_from_document(doc, payload, "M.F")

    assert declaration is not None
    # out-of-section end: the declaration keeps its own length.
    assert declaration.end_line_pos == 41 + (5 - 1)


def test_documents_outside_the_sections_are_ignored() -> None:
    payload = payload_with(
        [
            "private theorem shrink : True := trivial",  # p1
        ],
    )
    doc = document_for(0, 1)

    assert _decl_from_document(doc, payload, "M.F") is None
