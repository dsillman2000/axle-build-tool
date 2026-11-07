"""Unit tests for declaration stubbing (the `--sorry` machinery).

`stubbed_source` replaces each stubbed declaration's line span with a
single stub line built from the extracted signature — span replacement
*inside the file's own text*, so namespace/section/variable context
survives by construction.
"""

from __future__ import annotations

from datetime import datetime, timezone

from axle_build_tool.manifest import ExtractedDecl, ManifestNode
from axle_build_tool.stubbing import GRANTED_KINDS, stubbed_source

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


SCOPED_SOURCE = "\n".join(
    [
        "def base : Nat := 1",                          # 1
        "",                                             # 2
        "set_option maxHeartbeats 400000 in",           # 3
        "/-- scoped doc -/",                            # 4
        "theorem scoped_a : base = 1 := by",            # 5
        "  simp [base]",                                # 6
        "",                                             # 7
        "set_option maxHeartbeats 400000 in",           # 8
        "theorem scoped_b : base * 2 = 2 := by",        # 9
        "  simp [base]",                                # 10
        "",                                             # 11
        "theorem tail : base = 1 := rfl",               # 12
    ]
) + "\n"

SCOPED_DECLS = [
    decl("base", "def", 1, 1, "def base : Nat"),
    decl("scoped_a", "theorem", 5, 6, "theorem scoped_a : base = 1"),
    decl("scoped_b", "theorem", 9, 10, "theorem scoped_b : base * 2 = 2"),
    decl("tail", "theorem", 12, 12, "theorem tail : base = 1"),
]


class TestTrimAbsorbsScopedOptionPrefixes:
    """Trimming a declaration takes its `set_option … in` prefixes with it.

    Lean attaches a scoped-option prefix line to the declaration whose
    span follows; a trim that leaves the prefix behind detaches it — at
    worst stranding `set_option … in` as the payload's last content,
    which fails to parse outright (issue 41).
    """

    def transform(self, keep, source=SCOPED_SOURCE, declarations=SCOPED_DECLS):
        from axle_build_tool.payloads import _NOT_STUBBED, _transform_member_source

        warnings: list[str] = []
        transformed, orig = _transform_member_source(
            self.node_with(declarations), source, _NOT_STUBBED, frozenset(keep), warnings
        )
        return transformed, orig

    @staticmethod
    def node_with(declarations) -> ManifestNode:
        return NODE.model_copy(update={"declarations": declarations})

    def test_trimming_scoped_declarations_leaves_no_dangling_prefix(self) -> None:
        transformed, _orig = self.transform({"base", "tail"})

        assert "set_option" not in transformed, transformed
        assert "def base : Nat := 1" in transformed
        assert "theorem tail : base = 1 := rfl" in transformed
        assert "scoped_a" not in transformed
        assert "scoped_b" not in transformed

    def test_prefix_above_docstring_absorbs_both(self) -> None:
        source = "\n".join(
            [
                "def x : Nat := 1",                        # 1
                "",                                        # 2
                "set_option maxHeartbeats 400000 in",      # 3
                "/-- doc -/",                              # 4
                "theorem dd : x = 1 := rfl",               # 5
            ]
        ) + "\n"
        transformed, _orig = self.transform(
            {"x"},
            source=source,
            declarations=[decl("x", "def", 1, 1, "def x : Nat"),
                          decl("dd", "theorem", 5, 5, "theorem dd : x = 1")],
        )

        assert transformed == "def x : Nat := 1\n", transformed

    def test_prefix_below_docstring_absorbs_both(self) -> None:
        source = "\n".join(
            [
                "def x : Nat := 1",                        # 1
                "",                                        # 2
                "/-- doc -/",                              # 3
                "set_option maxHeartbeats 400000 in",      # 4
                "theorem dd : x = 1 := rfl",               # 5
            ]
        ) + "\n"
        transformed, _orig = self.transform(
            {"x"},
            source=source,
            declarations=[decl("x", "def", 1, 1, "def x : Nat"),
                          decl("dd", "theorem", 5, 5, "theorem dd : x = 1")],
        )

        assert transformed == "def x : Nat := 1\n", transformed

    def test_chained_prefixes_absorb_together(self) -> None:
        source = "\n".join(
            [
                "def x : Nat := 1",                        # 1
                "",                                        # 2
                "set_option pp.all true in",               # 3
                "set_option maxHeartbeats 400000 in",      # 4
                "/-- doc -/",                              # 5
                "theorem dd : x = 1 := rfl",               # 6
            ]
        ) + "\n"
        transformed, _orig = self.transform(
            {"x"},
            source=source,
            declarations=[decl("x", "def", 1, 1, "def x : Nat"),
                          decl("dd", "theorem", 6, 6, "theorem dd : x = 1")],
        )

        assert transformed == "def x : Nat := 1\n", transformed

    def test_bare_set_option_without_in_stays(self) -> None:
        """A section-scoped option (no `in`) belongs to the section, not
        to the next declaration — it must survive the trim."""
        source = "\n".join(
            [
                "def x : Nat := 1",                        # 1
                "",                                        # 2
                "set_option maxHeartbeats 800000",         # 3
                "/-- doc -/",                              # 4
                "theorem dd : x = 1 := rfl",               # 5
            ]
        ) + "\n"
        transformed, _orig = self.transform(
            {"x"},
            source=source,
            declarations=[decl("x", "def", 1, 1, "def x : Nat"),
                          decl("dd", "theorem", 5, 5, "theorem dd : x = 1")],
        )

        assert "set_option maxHeartbeats 800000" in transformed, transformed
        assert "theorem dd" not in transformed

    def test_line_comment_mentioning_the_form_is_not_absorbed(self) -> None:
        source = "\n".join(
            [
                "def x : Nat := 1",                        # 1
                "",                                        # 2
                "-- set_option maxHeartbeats 400000 in",   # 3
                "/-- doc -/",                              # 4
                "theorem dd : x = 1 := rfl",               # 5
            ]
        ) + "\n"
        transformed, _orig = self.transform(
            {"x"},
            source=source,
            declarations=[decl("x", "def", 1, 1, "def x : Nat"),
                          decl("dd", "theorem", 5, 5, "theorem dd : x = 1")],
        )

        assert "-- set_option maxHeartbeats 400000 in" in transformed, transformed

    def test_kept_declaration_keeps_its_prefix_and_docstring(self) -> None:
        transformed, _orig = self.transform({"base", "scoped_a"})

        assert "set_option maxHeartbeats 400000 in" in transformed, transformed
        assert "/-- scoped doc -/" in transformed
        assert "theorem scoped_a : base = 1 := by" in transformed
        # The dropped sibling's prefix went with it.
        assert transformed.count("set_option") == 1, transformed
        assert "scoped_b" not in transformed

    def test_prefix_boundary_is_the_previous_kept_content(self) -> None:
        """The absorb walk stops on the first line that neither ends a
        docstring nor opens a scoped-option prefix — a kept sibling's
        own content is never consumed."""
        source = "\n".join(
            [
                "theorem kept : True := rfl",              # 1
                "set_option maxHeartbeats 400000 in",      # 2
                "theorem dd : True := rfl",                # 3
            ]
        ) + "\n"
        transformed, _orig = self.transform(
            {"kept"},
            source=source,
            declarations=[decl("kept", "theorem", 1, 1, "theorem kept : True"),
                          decl("dd", "theorem", 3, 3, "theorem dd : True")],
        )

        assert transformed.splitlines()[0] == "theorem kept : True := rfl", transformed
        assert "set_option" not in transformed

    def test_absorbed_trims_stay_a_strict_partition(self) -> None:
        transformed, orig = self.transform({"base", "tail"})

        non_stub = [line for line in orig if line is not None]
        assert len(non_stub) == len(set(non_stub)), non_stub
        assert "set_option" not in transformed

class TestStubbedSource:
    def test_stubbed_bodies_keep_signatures_and_context(self) -> None:
        result = stubbed_source(stubbed_node(DECLS), SOURCE)

        assert result == (
            "import Mathlib\n"
            "\n"
            "namespace Algebra\n"
            "\n"
            "/-- doc for base -/\n"
            "def base : Nat := 1\n"              # defs keep their real body
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

    def test_default_stubs_every_granted_proof_declaration(self) -> None:
        node = stubbed_node(DECLS)

        result = stubbed_source(node, SOURCE)

        assert "def base : Nat := 1" in result  # def bodies stay real
        assert "theorem uses_base : base = 1 := by sorry" in result
        assert "theorem gap : 2 + 2 = 5 := by sorry" in result

    def test_abbrev_keeps_its_real_body(self) -> None:
        """Definitional bodies are content downstream proofs unfold;
        grants excuse abbrevs without touching them."""
        node = stubbed_node([decl("myNat", "abbrev", 1, 1, "abbrev myNat : Nat")])

        result = stubbed_source(node, "abbrev myNat : Nat := 1\n")

        assert result == "abbrev myNat : Nat := 1\n"

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
        source = (
            "theorem first : True := rfl\nline two\nline three\nline four\n"
        )

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

    def test_granted_kinds_are_exactly_the_body_bearing_ones(self) -> None:
        """Grants cover proof kinds (stubbed) plus the definitional
        kinds (excused with their real bodies)."""
        assert GRANTED_KINDS == {
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


class TestUnderStubbingWarnings:
    """A requested stub that can't be applied warns, naming the file and
    the prescription — it must never silently submit un-stubbed code."""

    def test_misaligned_span_warns_and_is_skipped(self) -> None:
        """A source edited after compiling: the span no longer starts at
        the declaration's keyword — the staleness tell."""
        node = stubbed_node([decl("t", "theorem", 1, 1, "theorem t : 1 = 1")])
        source = "-- a new comment line\ntheorem t : 1 = 1 := rfl\n"
        warnings: list[str] = []

        result = stubbed_source(node, source, warnings=warnings)

        assert result == source  # untouched: never stub garbage
        assert len(warnings) == 1
        assert "M/A.lean" in warnings[0]
        assert "'t' could not be stubbed" in warnings[0]
        assert "run `axbt compile`" in warnings[0]

    def test_out_of_range_span_warns(self) -> None:
        node = stubbed_node([decl("t", "theorem", 9, 10, "theorem t : 1 = 1")])
        warnings: list[str] = []

        stubbed_source(node, "theorem t : 1 = 1 := rfl\n", warnings=warnings)

        assert len(warnings) == 1
        assert "run `axbt compile`" in warnings[0]

    def test_healthy_spans_warn_nothing(self) -> None:
        node = stubbed_node(
            [decl("t", "theorem", 2, 2, "theorem t : 1 = 1")]
        )
        source = "/-- doc -/\ntheorem t : 1 = 1 := rfl\n"
        warnings: list[str] = []

        result = stubbed_source(node, source, warnings=warnings)

        assert warnings == []
        assert result == "/-- doc -/\ntheorem t : 1 = 1 := by sorry\n"

    def test_snap_fallback_docstring_position_is_accepted(self) -> None:
        """Rare snap fallback: the recorded position sits ON the
        docstring — still trusted (it is the extraction's own record)."""
        node = stubbed_node(
            [decl("t", "theorem", 1, 2, "/-- doc -/\ntheorem t : 1 = 1")]
        )
        source = "/-- doc -/\ntheorem t : 1 = 1 := rfl\n"
        warnings: list[str] = []

        result = stubbed_source(node, source, warnings=warnings)

        assert warnings == []
        assert result == "theorem t : 1 = 1 := by sorry\n"

    def test_no_warnings_argument_stays_quiet(self) -> None:
        node = stubbed_node([decl("t", "theorem", 9, 10, "theorem t : 1 = 1")])

        assert stubbed_source(node, "theorem t : 1 = 1 := rfl\n") == (
            "theorem t : 1 = 1 := rfl\n"
        )


class TestSpanHeadMatches:
    """The span-head check: which first lines can carry a declaration."""

    def test_modifier_prefixed_heads_match_their_kind(self) -> None:
        from axle_build_tool.stubbing import _span_head_matches

        assert _span_head_matches("private theorem twoPowSq : …", "theorem")
        assert _span_head_matches("private def base := 1", "def")
        assert _span_head_matches("protected def middle := 1", "def")
        assert _span_head_matches("noncomputable def f : Nat := 0", "def")
        assert _span_head_matches("unsafe def f : Nat := 0", "def")
        assert _span_head_matches("partial def f : Nat → Nat", "def")
        assert _span_head_matches("@[simp] theorem sniffed : True", "theorem")
        assert _span_head_matches("  private lemma tucked : True", "lemma")

    def test_other_kinds_and_misaligned_heads_do_not_match(self) -> None:
        from axle_build_tool.stubbing import _span_head_matches

        assert not _span_head_matches("private theorem twoPowSq : …", "def")
        assert not _span_head_matches("rw [twoPow]", "theorem")
        assert not _span_head_matches("end KaratsubaSqrt", "theorem")
        # The docstring fallback stays accepted (extraction's own record).
        assert _span_head_matches("  /-- docstring -/", "theorem")


class TestTransformMemberSourcePartition:
    """`_transform_member_source` is a strict partition of the source.

    Stale or corrupt spans degrade a declaration to its real text;
    they may never duplicate content, whatever the manifest carries.
    """

    @staticmethod
    def node_with(declarations) -> ManifestNode:
        return NODE.model_copy(update={"declarations": declarations})

    SOURCE = "\n".join(
        [
            "import Dep",                                                       # 1
            "",                                                                 # 2
            "namespace Sqrt",                                                   # 3
            "",                                                                 # 4
            "private theorem addZero : Nat.zero = Nat.zero := rfl",             # 5
            "private theorem twoPowSq : Nat.one = Nat.one := by",               # 6
            "  rw [Nat.one_def]",                                               # 7
            "private theorem powSqSucc : Nat.two = Nat.two := by",              # 8
            "  rw [Nat.two_def]",                                               # 9
            "",                                                                 # 10
            "theorem guardrail_39999_total : Nat.four = Nat.four := by",        # 11
            "  sorry",                                                          # 12
            "",                                                                 # 13
            "end Sqrt",                                                         # 14
        ]
    ) + "\n"

    #: The exact corruption shape issue 38 reports: several sibling
    #: `private theorem`s whose `line_pos` snapped forward onto the
    #: guardrail target's line, so their spans read inverted or
    #: overlapping against their recorded ends.
    CORRUPT_DECLS = [
        decl("addZero", "theorem", 11, 5, "private theorem addZero : Nat.zero = Nat.zero"),
        decl("twoPowSq", "theorem", 11, 7, "private theorem twoPowSq : Nat.one = Nat.one"),
        decl("powSqSucc", "theorem", 11, 9, "private theorem powSqSucc : Nat.two = Nat.two"),
        decl("guardrail_39999_total", "theorem", 11, 12, "theorem guardrail_39999_total : Nat.four = Nat.four"),
    ]

    def test_snapped_forward_spans_emit_each_sibling_once(self) -> None:
        from axle_build_tool.payloads import _transform_member_source

        node = self.node_with(self.CORRUPT_DECLS)
        warnings: list[str] = []

        transformed, orig = _transform_member_source(
            node, self.SOURCE, frozenset(["guardrail_39999_total"]), None, warnings
        )

        for header in (
            "private theorem addZero",
            "private theorem twoPowSq",
            "private theorem powSqSucc",
            "theorem guardrail_39999_total",
        ):
            assert transformed.count(header) == 1, transformed
        # The grant is honored: the guardrail's proof is stubbed.
        assert (
            "theorem guardrail_39999_total : Nat.four = Nat.four := by sorry"
            in transformed
        )
        # Sibling bodies (not granted) keep their real text.
        assert "  rw [Nat.one_def]" in transformed
        assert "  rw [Nat.two_def]" in transformed
        # The untreatable spans are called out, once per declaration.
        assert len(warnings) == 3
        for warning in warnings:
            assert "M/A.lean" in warning
            assert "run `axbt compile`" in warning

    def test_the_walk_never_emits_a_source_line_twice(self) -> None:
        from axle_build_tool.payloads import _transform_member_source

        # Two flavors of corrupt data at once: inverted sibling spans
        # and one that swallows the next declaration's lines.
        spans = list(self.CORRUPT_DECLS) + [
            decl("overshooting", "theorem", 11, 13, "theorem overshooting : True")
        ]
        node = self.node_with(spans)
        warnings: list[str] = []

        transformed, orig = _transform_member_source(
            node, self.SOURCE, frozenset(["guardrail_39999_total"]), None, warnings
        )

        non_stub = [line for line in orig if line is not None]
        assert len(non_stub) == len(set(non_stub)), non_stub

    def test_overlapping_healthy_spans_cannot_swallow_a_sibling(self) -> None:
        """A span reaching past the next declaration is clamped, so a
        stub never consumes (or later re-emits) a sibling's lines."""
        from axle_build_tool.payloads import _transform_member_source

        node = self.node_with(
            [
                # `outer`'s recorded end includes the guardrail's header.
                decl("outer", "theorem", 6, 12, "private theorem outer : True"),
                decl("guardrail_39999_total", "theorem", 11, 12, "theorem guardrail_39999_total : Nat.four = Nat.four"),
            ]
        )
        warnings: list[str] = []

        transformed, orig = _transform_member_source(
            node, self.SOURCE, frozenset(["guardrail_39999_total"]), None, warnings
        )

        assert transformed.count("theorem guardrail_39999_total") == 1
        assert (
            "theorem guardrail_39999_total : Nat.four = Nat.four := by sorry"
            in transformed
        )

    def test_module_level_grant_stubs_private_siblings(self) -> None:
        """With every proof declaration granted, modifier heads are
        stubbed like any other (the pre-#38 transform left them real)."""
        from axle_build_tool.payloads import _transform_member_source

        node = self.node_with(
            [
                decl("addZero", "theorem", 5, 5, "private theorem addZero : Nat.zero = Nat.zero"),
                decl("twoPowSq", "theorem", 6, 7, "private theorem twoPowSq : Nat.one = Nat.one"),
            ]
        )
        source = self.SOURCE

        transformed, _orig = _transform_member_source(
            node, source, None, None, None
        )

        assert (
            "private theorem addZero : Nat.zero = Nat.zero := by sorry" in transformed
        )
        assert (
            "private theorem twoPowSq : Nat.one = Nat.one := by sorry" in transformed
        )
        assert "  rw [Nat.one_def]" not in transformed
