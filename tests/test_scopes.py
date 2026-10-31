"""Unit tests for the Lean 4 scope-structure parser.

These demonstrate how each scoping construct Lean 4 offers —
`namespace` (incl. dotted and nested), `section` (incl. anonymous and
named), `variable` (all binder forms, shadowing, section lifetime), and
`open` (multi-namespace, `hiding`, `renaming`, `scoped`, and the
transient `open ... in` forms) — is accounted for by `parse_scopes`,
alongside the comment forms that must hide scope keywords.
"""

from __future__ import annotations

from axle_build_tool.scopes import ScopeHeader, parse_scopes

#: A scope snapshot reduced to comparable (kind, text) pairs.
def scope_of(scopes, line: int) -> list[tuple[str, str]]:
    return [(header.kind, header.text) for header in scopes.at(line)]


class TestNamespaces:
    def test_namespace_is_active_for_its_interior(self) -> None:
        scopes = parse_scopes(
            "namespace Algebra\ntheorem t : 1 = 1 := rfl\nend Algebra\n"
        )

        assert scope_of(scopes, 2) == [("namespace", "namespace Algebra")]
        assert scopes.at(2)[0].line == 1

    def test_nested_namespaces_stack_in_document_order(self) -> None:
        scopes = parse_scopes(
            "namespace A\nnamespace B\ntheorem deep : 1 = 1 := rfl\nend B\n"
            "theorem shallow : 1 = 1 := rfl\nend A\n"
        )

        assert scope_of(scopes, 3) == [
            ("namespace", "namespace A"),
            ("namespace", "namespace B"),
        ]
        # `end B` pops only B...
        assert scope_of(scopes, 5) == [("namespace", "namespace A")]
        # ...and the second `end` leaves the top level.
        assert scopes.at(7) == ()

    def test_dotted_namespace_is_a_single_scope(self) -> None:
        scopes = parse_scopes(
            "namespace Foo.Bar\ntheorem t : 1 = 1 := rfl\nend Foo.Bar\n"
        )

        assert scope_of(scopes, 2) == [("namespace", "namespace Foo.Bar")]
        # Line 3 is the `end` line (the scope is active there); it is
        # gone from line 4 on.
        assert scope_of(scopes, 3) == [("namespace", "namespace Foo.Bar")]
        assert scopes.at(4) == ()

    def test_reopened_namespace_is_active_again(self) -> None:
        scopes = parse_scopes(
            "namespace A\nend A\nnamespace A\ntheorem t : 1 = 1 := rfl\nend A\n"
        )

        # Lines 1, 2 (its `end`), 3 (the reopen), 4, 5 (its `end`).
        assert scope_of(scopes, 2) == [("namespace", "namespace A")]
        assert scope_of(scopes, 3) == [("namespace", "namespace A")]
        assert scope_of(scopes, 4) == [("namespace", "namespace A")]
        assert scope_of(scopes, 5) == [("namespace", "namespace A")]
        assert scopes.at(6) == ()

    def test_end_names_are_not_required_to_match(self) -> None:
        """A mismatched `end` name is a Lean error, not a parser error;
        the parser pops the innermost scope either way."""
        scopes = parse_scopes("namespace A\nend Wrong\n")

        assert scopes.at(2) == scopes.at(1)
        assert scopes.at(3) == ()  # wait: line 3 is beyond the file

    def test_preamble_renders_namespace_nesting(self) -> None:
        scopes = parse_scopes("namespace A\nnamespace B\ntheorem t : 1 = 1 := rfl\n")

        assert scopes.preamble_at(3) == "namespace A\nnamespace B"


class TestSections:
    def test_anonymous_section_is_active(self) -> None:
        scopes = parse_scopes("section\ntheorem t : 1 = 1 := rfl\nend\n")

        assert scope_of(scopes, 2) == [("section", "section")]
        assert scope_of(scopes, 3) == [("section", "section")]  # at its `end`
        assert scopes.at(4) == ()

    def test_named_section_is_recorded_with_its_name(self) -> None:
        scopes = parse_scopes("section helpers\ntheorem t : 1 = 1 := rfl\nend helpers\n")

        assert scope_of(scopes, 2) == [("section", "section helpers")]

    def test_section_inside_namespace_keeps_both(self) -> None:
        scopes = parse_scopes(
            "namespace A\nsection s\ntheorem t : 1 = 1 := rfl\nend s\nend A\n"
        )

        assert scope_of(scopes, 3) == [
            ("namespace", "namespace A"),
            ("section", "section s"),
        ]
        # Line 4 is `end s`: the section is still active there...
        assert scope_of(scopes, 4) == [
            ("namespace", "namespace A"),
            ("section", "section s"),
        ]
        # ...and gone from line 5 (`end A`), where only the namespace remains.
        assert scope_of(scopes, 5) == [("namespace", "namespace A")]
        assert scopes.at(6) == ()


class TestVariables:
    def test_variable_is_active_for_following_declarations(self) -> None:
        scopes = parse_scopes("variable (n : Nat)\ntheorem t : n = n := rfl\n")

        assert scope_of(scopes, 2) == [("variable", "variable (n : Nat)")]

    def test_variable_lines_accumulate_in_order(self) -> None:
        scopes = parse_scopes(
            "variable (n : Nat)\nvariable (m : Nat)\ntheorem t : n = m := rfl\n"
        )

        assert scope_of(scopes, 3) == [
            ("variable", "variable (n : Nat)"),
            ("variable", "variable (m : Nat)"),
        ]

    def test_binder_forms_are_all_variables(self) -> None:
        scopes = parse_scopes(
            "variable {α : Type}\nvariable [inst : α]\nvariable (p : α → Prop)\n"
            "theorem t : True := True.intro\n"
        )

        assert scope_of(scopes, 4) == [
            ("variable", "variable {α : Type}"),
            ("variable", "variable [inst : α]"),
            ("variable", "variable (p : α → Prop)"),
        ]

    def test_redeclared_variable_keeps_both_lines(self) -> None:
        """Lean shadows a re-declared variable; the model records both
        header lines in order (the later one wins downstream)."""
        scopes = parse_scopes(
            "variable (n : Nat)\nvariable (n : Int)\ntheorem t : True := True.intro\n"
        )

        assert scope_of(scopes, 3) == [
            ("variable", "variable (n : Nat)"),
            ("variable", "variable (n : Int)"),
        ]

    def test_file_level_variables_survive_section_boundaries(self) -> None:
        scopes = parse_scopes(
            "variable (n : Nat)\nsection s\ntheorem t : n = n := rfl\nend s\n"
            "theorem u : n = n := rfl\n"
        )

        inside = scope_of(scopes, 3)
        assert inside == [
            ("variable", "variable (n : Nat)"),
            ("section", "section s"),
        ]
        # The section's end removes the section, not the variable.
        assert scope_of(scopes, 5) == [("variable", "variable (n : Nat)")]


class TestOpens:
    def test_open_is_active_for_following_declarations(self) -> None:
        scopes = parse_scopes("open Nat\ntheorem t : 1 = 1 := rfl\n")

        assert scope_of(scopes, 2) == [("open", "open Nat")]

    def test_multi_namespace_open_is_one_header(self) -> None:
        scopes = parse_scopes("open Nat Int\ntheorem t : 1 = 1 := rfl\n")

        assert scope_of(scopes, 2) == [("open", "open Nat Int")]

    def test_hiding_renaming_and_scoped_forms_are_opens(self) -> None:
        scopes = parse_scopes(
            "open Nat hiding zero\nopen Foo renaming a → b\nopen scoped Nat\n"
            "theorem t : 1 = 1 := rfl\n"
        )

        assert scope_of(scopes, 4) == [
            ("open", "open Nat hiding zero"),
            ("open", "open Foo renaming a → b"),
            ("open", "open scoped Nat"),
        ]

    def test_open_ends_with_its_scope(self) -> None:
        scopes = parse_scopes(
            "namespace A\nopen Nat\nend A\ntheorem t : 1 = 1 := rfl\n"
        )

        assert scope_of(scopes, 2) == [
            ("namespace", "namespace A"),
            ("open", "open Nat"),
        ]
        # Line 3 is the `end` (still active); the theorem at line 4 is
        # outside everything.
        assert scope_of(scopes, 3) == [
            ("namespace", "namespace A"),
            ("open", "open Nat"),
        ]
        assert scopes.at(4) == ()

    def test_transient_open_same_line_applies_only_to_that_command(self) -> None:
        scopes = parse_scopes(
            "open Nat in theorem t : 1 = 1 := rfl\ntheorem u : 2 = 2 := rfl\n"
        )

        at_t = scope_of(scopes, 1)
        assert at_t == [("open", "open Nat")]
        assert scopes.at(1)[0].transient
        # The next command must NOT inherit the transient open.
        assert scopes.at(2) == ()

    def test_transient_open_next_line_survives_blank_lines(self) -> None:
        scopes = parse_scopes(
            "open Nat in\n\ntheorem t : 1 = 1 := rfl\n\ntheorem u : 2 = 2 := rfl\n"
        )

        # The blank does not consume the pending transient...
        assert scopes.at(2) == ()
        # ...the command's line carries it...
        assert scope_of(scopes, 3) == [("open", "open Nat")]
        assert scopes.at(3)[0].transient
        # ...and it never outlives that command.
        assert scopes.at(5) == ()

    def test_chained_transient_opens_all_apply_to_the_command(self) -> None:
        scopes = parse_scopes(
            "open Nat in\nopen Int in\ndef x := 1\ntheorem t : x = 1 := rfl\n"
        )

        assert scope_of(scopes, 3) == [("open", "open Nat"), ("open", "open Int")]
        assert scopes.at(4) == ()

    def test_transient_open_preamble_drops_the_dangling_in(self) -> None:
        scopes = parse_scopes("open Nat in\ntheorem t : 1 = 1 := rfl\n")

        assert scopes.preamble_at(2) == "open Nat"

    def test_transient_open_with_multiline_command_text(self) -> None:
        scopes = parse_scopes(
            "open Nat in theorem t :\n    1 = 1 := rfl\ntheorem u : 2 = 2 := rfl\n"
        )

        assert scope_of(scopes, 1) == [("open", "open Nat")]
        assert scopes.at(3) == ()


class TestComments:
    def test_line_comment_after_header(self) -> None:
        scopes = parse_scopes("namespace A -- entry\ntheorem t : 1 = 1 := rfl\n")

        assert scope_of(scopes, 2) == [("namespace", "namespace A")]

    def test_commented_out_headers_are_ignored(self) -> None:
        scopes = parse_scopes(
            "-- namespace Fake\n-- section fake\ntheorem t : 1 = 1 := rfl\n"
        )

        assert scopes.at(3) == ()

    def test_block_commented_headers_are_ignored(self) -> None:
        scopes = parse_scopes(
            "/- namespace Fake\nsection fake -/\ntheorem t : 1 = 1 := rfl\n"
        )

        assert scopes.at(3) == ()

    def test_nested_block_comments_are_ignored(self) -> None:
        scopes = parse_scopes(
            "/- outer /- inner namespace Fake -/ still fake -/\n"
            "theorem t : 1 = 1 := rfl\n"
        )

        assert scopes.at(3) == ()

    def test_docstrings_do_not_open_scopes(self) -> None:
        scopes = parse_scopes(
            "/-- The doc mentions `namespace Fake` and `variable (x : Nat)`. -/\n"
            "theorem t : 1 = 1 := rfl\n"
        )

        assert scopes.at(2) == ()


class TestEdges:
    def test_empty_file(self) -> None:
        assert parse_scopes("").at(1) == ()

    def test_blank_and_comment_only_file(self) -> None:
        scopes = parse_scopes("\n\n-- nothing\n/- still nothing -/\n")

        assert scopes.at(1) == ()
        assert scopes.at(3) == ()
        assert scopes.at(4) == ()

    def test_end_on_an_empty_stack_is_tolerated(self) -> None:
        """A top-level `end` is a Lean error; the parser stays lenient."""
        scopes = parse_scopes("end\ntheorem t : 1 = 1 := rfl\n")

        assert scopes.at(2) == ()

    def test_out_of_range_lines_resolve_to_no_scope(self) -> None:
        scopes = parse_scopes("namespace A\nend A\n")

        assert scopes.at(0) == ()
        assert scopes.at(99) == ()

    def test_top_level_content_has_no_scope(self) -> None:
        scopes = parse_scopes("def x := 1\ntheorem t : x = 1 := rfl\n")

        assert scopes.at(1) == ()
        assert scopes.at(2) == ()

    def test_every_line_receives_a_snapshot(self) -> None:
        source = "namespace A\n\n-- note\ntheorem t : 1 = 1 := rfl\nend A\n"
        scopes = parse_scopes(source)

        for line in range(1, len(source.splitlines()) + 1):
            assert line in scopes.snapshots, line

    def test_declaration_after_scope_closes_has_no_scope(self) -> None:
        scopes = parse_scopes(
            "namespace A\nsection s\nend s\nend A\ndef x := 1\n"
        )

        assert scopes.at(5) == ()


class TestKitchenSink:
    """A realistic file combining every construct; the preambles for two
    deep declarations reconstruct exactly the headers they sit under."""

    SOURCE = """\
import Mathlib

namespace Algebra
/-
  a block comment that mentions
  /- nested -/ namespace Fake
  and section Fake
-/
variable (n : Nat)

/-! Group theory helpers. -/

open Nat

section Helpers
variable (m : Nat)

/-- helper -/
theorem helper : m = m := rfl

end Helpers

theorem after : n = n := rfl

end Algebra

theorem outside : 1 = 1 := rfl
"""

    def test_deep_declaration_preamble(self) -> None:
        scopes = parse_scopes(self.SOURCE)

        # `helper` sits in namespace + section, under two variables and
        # an open — all in document order.
        assert scopes.preamble_at(19) == (
            "namespace Algebra\n"
            "variable (n : Nat)\n"
            "open Nat\n"
            "section Helpers\n"
            "variable (m : Nat)"
        )
        assert [kind for kind, _ in scope_of(scopes, 19)] == [
            "namespace",
            "variable",
            "open",
            "section",
            "variable",
        ]

    def test_preamble_after_the_section_closes(self) -> None:
        scopes = parse_scopes(self.SOURCE)

        assert scopes.preamble_at(23) == (
            "namespace Algebra\nvariable (n : Nat)\nopen Nat"
        )

    def test_preamble_outside_every_scope_is_empty(self) -> None:
        scopes = parse_scopes(self.SOURCE)

        assert scopes.preamble_at(27) == ""
