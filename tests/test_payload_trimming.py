"""Unit tests for upward trim extension in `_transform_member_source` (issue #52)."""

from __future__ import annotations

from axle_build_tool.manifest import ExtractedDecl, ManifestNode
from axle_build_tool.payloads import _NOT_STUBBED, _transform_member_source


def _node(declarations: list[ExtractedDecl]) -> ManifestNode:
    return ManifestNode(
        name="M.A",
        module="M",
        path="M/A.lean",
        md5="0" * 32,
        status="clean",
        declarations=declarations,
    )


def _decl(name: str, line_pos: int, end_line_pos: int, kind: str = "theorem") -> ExtractedDecl:
    return ExtractedDecl(
        name=name,
        kind=kind,
        is_sorry=False,
        line_pos=line_pos,
        end_line_pos=end_line_pos,
        signature=f"{kind} {name}",
    )


def test_inline_block_comment_on_kept_code_line_is_not_wiped() -> None:
    """A non-declaration code line ending in `/- ... -/` preceded by an
    earlier `/- ... -/` comment must survive when the next decl is trimmed."""
    source = (
        "/- header -/\n"
        "open Foo /- inline comment -/\n"
        "theorem drop : True := trivial\n"
        "def keep := 1\n"
    )
    node = _node([
        _decl("drop", 3, 3, kind="theorem"),
        _decl("keep", 4, 4, kind="def"),
    ])
    transformed, _ = _transform_member_source(
        node, source, _NOT_STUBBED, keep_names={"keep"}
    )
    assert "/- header -/" in transformed
    assert "open Foo /- inline comment -/" in transformed
    assert "theorem drop" not in transformed
    assert "def keep := 1" in transformed


def test_multiline_comment_starting_after_code_is_not_wiped() -> None:
    source = (
        "open Foo /- start\n"
        "  end -/\n"
        "theorem drop : True := trivial\n"
        "def keep := 1\n"
    )
    node = _node([
        _decl("drop", 3, 3, kind="theorem"),
        _decl("keep", 4, 4, kind="def"),
    ])
    transformed, _ = _transform_member_source(
        node, source, _NOT_STUBBED, keep_names={"keep"}
    )
    assert "open Foo /- start" in transformed
    assert "theorem drop" not in transformed
    assert "def keep := 1" in transformed


def test_open_in_and_standalone_attr_prefixes_are_trimmed() -> None:
    source = (
        "def keep := 1\n"
        "open Nat in\n"
        "theorem drop1 : True := trivial\n"
        "@[simp]\n"
        "theorem drop2 : True := trivial\n"
    )
    node = _node([
        _decl("keep", 1, 1, kind="def"),
        _decl("drop1", 3, 3, kind="theorem"),
        _decl("drop2", 5, 5, kind="theorem"),
    ])
    transformed, _ = _transform_member_source(
        node, source, _NOT_STUBBED, keep_names={"keep"}
    )
    assert transformed == "def keep := 1\n"


def test_chained_doc_attr_open_set_option_prefixes_are_trimmed() -> None:
    source = (
        "def keep := 1\n"
        "/--\n"
        "  multiline doc\n"
        "-/\n"
        "@[simp, inline]\n"
        "open Nat in\n"
        "set_option pp.all true in\n"
        "theorem drop : True := trivial\n"
    )
    node = _node([
        _decl("keep", 1, 1, kind="def"),
        _decl("drop", 8, 8, kind="theorem"),
    ])
    transformed, _ = _transform_member_source(
        node, source, _NOT_STUBBED, keep_names={"keep"}
    )
    assert transformed == "def keep := 1\n"
