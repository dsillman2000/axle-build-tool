"""Unit tests for declaration stubbing (plan §5's `--sorry` machinery).

`stubbed_source` replaces each stubbed declaration's line span with a
single stub line built from the extracted signature — span replacement
*inside the file's own text*, so namespace/section/variable context
survives by construction.
"""

from __future__ import annotations

from datetime import datetime, timezone

from axle_build_tool.manifest import ExtractedDecl, ManifestNode
from axle_build_tool.stubbing import STUBBABLE_KINDS, stubbed_source

NODE = ManifestNode(
    name="M.A",
    module="M",
    path="M/A.lean",
    md5="0" * 32,
    status="clean",
    request_id="req-0001",
    last_checked=datetime(2026, 10, 31, tzinfo=timezone.utc),
)


def decl(
    name: str,
    kind: str,
    line_pos: int,
    end_line_pos: int,
    signature: str,
) -> ExtractedDecl:
    return ExtractedDecl(
        name=name,
        kind=kind,
        is_sorry=False,
        line_pos=line_pos,
        end_line_pos=end_line_pos,
        signature=signature,
    )


#: A realistic mixed-kind file (line numbers in comments).
SOURCE = "\n".join(
    [
        "import Mathlib",                       # 1
        "",                                     # 2
        "namespace Algebra",                    # 3
        "",                                     # 4
        "/-- doc for base -/",                  # 5
        "def base : Nat := 1",                  # 6
        "",                                     # 7
        "theorem uses_base : base = 1 := rfl",  # 8
        "",                                     # 9
        "structure W where",                    # 10
        "  value : Nat",                        # 11
        "",                                     # 12
        "instance : Inhabited W := ⟨⟨1⟩⟩",      # 13
        "",                                     # 14
        "theorem gap : 2 + 2 = 5 := by sorry",  # 15
        "",                                     # 16
        "end Algebra",                          # 17
    ]
) + "\n"

DECLS = [
    decl("base", "def", 6, 6, "def base : Nat"),
    decl("uses_base", "theorem", 8, 8, "theorem uses_base : base = 1"),
    decl("W", "structure", 10, 11, "structure W"),
    decl("_instInhabitedW", "instance", 13, 13, "instance : Inhabited W"),
    decl("gap", "theorem", 15, 15, "theorem gap : 2 + 2 = 5"),
]


def stubbed_node(declarations) -> ManifestNode:
    return NODE.model_copy(update={"declarations": declarations})


class TestStubbedSource:
    def test_stubbed_bodies_keep_signatures_and_context(self) -> None:
        result = stubbed_source(stubbed_node(DECLS), SOURCE)

        assert result == (
            "import Mathlib\n"
            "\n"
            "namespace Algebra\n"
            "\n"
            "/-- doc for base -/\n"
            "def base : Nat := sorry\n"          # def body -> `:= sorry`
            "\n"
            "theorem uses_base : base = 1 := by sorry\n"  # proof -> `:= by sorry`
            "\n"
            "structure W where\n"                # structural kinds stay real...
            "  value : Nat\n"
            "\n"
            "instance : Inhabited W := ⟨⟨1⟩⟩\n"  # ...including instances
            "\n"
            "theorem gap : 2 + 2 = 5 := by sorry\n"
            "\n"
            "end Algebra\n"
        )

    def test_multiline_span_collapses_to_one_stub_line(self) -> None:
        source = (
            "namespace A\n"
            "theorem long (n : Nat) :\n"
            "    n = n :=\n"
            "  rfl\n"
            "end A\n"
        )
        node = stubbed_node(
            [decl("long", "theorem", 2, 4, "theorem long (n : Nat) : n = n")]
        )

        result = stubbed_source(node, source)

        assert result == (
            "namespace A\ntheorem long (n : Nat) : n = n := by sorry\nend A\n"
        )

    def test_signature_docstring_is_not_duplicated(self) -> None:
        """The docstring lines sit ABOVE the replaced span (the span
        starts at the keyword line) and re-attach to the stub; the
        signature's embedded docstring copy must not come back."""
        source = "/-- doc -/\ntheorem t : 1 = 1 := rfl\n"
        node = stubbed_node(
            [decl("t", "theorem", 2, 2, "/-- doc -/\ntheorem t : 1 = 1")]
        )

        result = stubbed_source(node, source)

        assert result == "/-- doc -/\ntheorem t : 1 = 1 := by sorry\n"
        assert result.count("/-- doc -/") == 1

    def test_multiline_docstring_in_signature_is_stripped(self) -> None:
        signature = "/-- first line\nsecond line -/\ntheorem t : 1 = 1"
        node = stubbed_node([decl("t", "theorem", 3, 3, signature)])
        source = "/-- first line\nsecond line -/\ntheorem t : 1 = 1 := rfl\n"

        result = stubbed_source(node, source)

        assert result.splitlines()[2] == "theorem t : 1 = 1 := by sorry"

    def test_signature_without_docstring_is_unchanged(self) -> None:
        node = stubbed_node([decl("t", "theorem", 1, 1, "theorem t : 1 = 1")])

        result = stubbed_source(node, "theorem t : 1 = 1 := rfl\n")

        assert result == "theorem t : 1 = 1 := by sorry\n"

    def test_only_restricts_stubbing_to_named_declarations(self) -> None:
        node = stubbed_node(DECLS)

        result = stubbed_source(node, SOURCE, only=frozenset({"uses_base"}))

        # base keeps its real body; uses_base is stubbed.
        assert "def base : Nat := 1" in result
        assert "theorem uses_base : base = 1 := by sorry" in result
        assert "theorem gap : 2 + 2 = 5 := by sorry" in result  # untouched (already sorry)

    def test_default_stubs_every_stubvable_declaration(self) -> None:
        node = stubbed_node(DECLS)

        result = stubbed_source(node, SOURCE)

        assert "def base : Nat := sorry" in result
        assert "theorem uses_base : base = 1 := by sorry" in result
        assert "theorem gap : 2 + 2 = 5 := by sorry" in result

    def test_abbrev_is_stubbed_with_definition_form(self) -> None:
        node = stubbed_node([decl("my Nat", "abbrev", 1, 1, "abbrev myNat : Nat")])

        result = stubbed_source(node, "abbrev myNat : Nat := 1\n")

        assert result == "abbrev myNat : Nat := sorry\n"

    def test_stale_spans_are_left_in_place(self) -> None:
        """Spans beyond the current source (or inverted) are skipped —
        a stale manifest must not corrupt the payload."""
        node = stubbed_node(
            [
                decl("future", "theorem", 99, 100, "theorem future : True"),
                decl("inverted", "theorem", 3, 2, "theorem inverted : True"),
            ]
        )
        source = "namespace A\nend A\n"

        assert stubbed_source(node, source) == source

    def test_overlapping_spans_are_skipped(self) -> None:
        node = stubbed_node(
            [
                decl("first", "theorem", 1, 3, "theorem first : True"),
                decl("second", "theorem", 2, 4, "theorem second : True"),
            ]
        )
        source = "line one\nline two\nline three\nline four\n"

        result = stubbed_source(node, source)

        assert result.splitlines()[0] == "theorem first : True := by sorry"
        # `second` overlaps `first`'s replaced span: left untouched.
        assert "theorem second : True := by sorry" not in result

    def test_empty_node_leaves_source_untouched(self) -> None:
        assert stubbed_source(stubbed_node([]), SOURCE) == SOURCE

    def test_unknown_kinds_are_never_stubbed(self) -> None:
        node = stubbed_node([decl("ax", "axiom", 1, 1, "axiom ax : True")])

        assert stubbed_source(node, "axiom ax : True := True.intro\n") == (
            "axiom ax : True := True.intro\n"
        )

    def test_stubvable_kinds_are_exactly_the_body_bearing_ones(self) -> None:
        assert STUBBABLE_KINDS == {
            "theorem",
            "lemma",
            "example",
            "def",
            "abbrev",
        }

    def test_lemma_and_example_use_the_proof_form(self) -> None:
        node = stubbed_node(
            [
                decl("l", "lemma", 1, 1, "lemma l : 1 = 1"),
                decl("e", "example", 2, 2, "example : 2 = 2"),
            ]
        )

        result = stubbed_source(node, "lemma l : 1 = 1 := rfl\nexample : 2 = 2 := rfl\n")

        assert result == "lemma l : 1 = 1 := by sorry\nexample : 2 = 2 := by sorry\n"
