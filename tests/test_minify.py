"""Unit tests for best-effort Lean minification (`axle_build_tool.minify`).

The minifier strips comments and blank lines from payload text while
keeping every surviving line tagged with its original source line, so
payload line maps attribute diagnostics exactly. Cases here pin the
state machine's hazards: strings and char literals that contain
comment-lookalikes, nested block comments, docstrings kept verbatim,
and the clean fallback (`None`) when text doesn't track.
"""

from __future__ import annotations

from axle_build_tool.minify import Minified, minify_lines


def text(source: str) -> str:
    minified = minify_lines(source)
    assert minified is not None
    return "\n".join(minified.lines) + "\n"


class TestCommentStripping:
    def test_line_comments_are_stripped_inline_and_alone(self) -> None:
        assert text("foo := 1 -- trailing note\nbar := 2\n") == "foo := 1\nbar := 2\n"
        assert text("-- a full-line comment\nfoo\n") == "foo\n"

    def test_block_comments_are_stripped_with_nesting(self) -> None:
        assert text("/- out /- in -/ still out -/\nfoo\n") == "foo\n"
        assert text("a /- c -/ b\n") == "a  b\n"

    def test_section_headers_are_stripped(self) -> None:
        assert text(
            "/-!\nsome prose\nacross lines\n-/\ntheorem t : 1 = 1 := rfl\n"
        ) == "theorem t : 1 = 1 := rfl\n"

    def test_comment_content_never_confuses_the_scanner(self) -> None:
        # `--` inside a comment is just text; a `/-` inside would nest
        # (as in Lean) — use closing boundaries the scanner can match.
        assert text("/- has -- and dashes -- inside -/\nfoo\n") == "foo\n"
        assert text("-- contains /- ... close -/ clearly\nfoo\n") == "foo\n"

    def test_newlines_inside_comments_are_preserved_not_joined(self) -> None:
        # Content on either side of a spanning comment survives on its
        # own source lines; nothing is merged.
        minified = minify_lines("foo := /-\ncomment\n-/ 1\nbar := 2\n")
        assert minified is not None
        assert minified.lines == ("foo :=", " 1", "bar := 2")
        assert minified.source_lines == (1, 3, 4)

    def test_blank_lines_and_trailing_whitespace_collapse(self) -> None:
        assert text("foo\n\n\n   \nbar   \n") == "foo\nbar\n"

    def test_empty_and_prose_only_files_minify_to_nothing(self) -> None:
        assert minify_lines("") == Minified((), ())
        assert minify_lines("/- only comments -/\n\n") == Minified((), ())


class TestStringAndCharLiterals:
    def test_string_content_with_comment_lookalikes_survives(self) -> None:
        source = 'check "not -- a comment"\nfoo := 1\n'
        assert text(source) == source

    def test_escaped_quotes_inside_strings(self) -> None:
        source = 'x := "a \\" b -- not end " -- genuinely\nfoo := 1\n'
        assert text(source) == 'x := "a \\" b -- not end "\nfoo := 1\n'

    def test_char_literal_with_raw_quote_is_not_a_string(self) -> None:
        # `'"'` would otherwise flip string state and hide comments.
        source = "c := '\"' -- a comment after a raw-quote char\nfoo := 1\n"
        assert text(source) == "c := '\"'\nfoo := 1\n"

    def test_identifier_tailed_apostrophes_are_plain_characters(self) -> None:
        # `x'`, `h''` are identifiers ending in apostrophes, not char
        # literals; stripping must proceed normally after them.
        source = "theorem x' : P' := by\n  simp [h'.1] -- done\n"
        assert text(source) == "theorem x' : P' := by\n  simp [h'.1]\n"

    def test_char_literal_starts_on_non_identifier_boundary(self) -> None:
        source = "have h : x = ('a' - 'A') := by decide\n"
        assert text(source) == source


class TestDocstrings:
    def test_declaration_docstrings_kept_verbatim(self) -> None:
        source = (
            "/-- Adds one, documented -- with -- dashes. -/\n"
            "def inc (n : Nat) := n + 1\n"
        )
        assert text(source) == source

    def test_multiline_docstrings_keep_their_prose(self) -> None:
        source = (
            "/-- Scheme:\n\n* point one -- with a dash;\n* point two -/\n"
            "theorem t : True := trivial\n"
        )
        # Verbatim means verbatim: the docstring's internal blank line
        # and all its whitespace survive.
        minified = minify_lines(source)
        assert minified is not None
        assert minified.lines == (
            "/-- Scheme:",
            "",
            "* point one -- with a dash;",
            "* point two -/",
            "theorem t : True := trivial",
        )
        assert minified.source_lines == (1, 2, 3, 4, 5)

    def test_docstring_then_code_line_numbering(self) -> None:
        minified = minify_lines("/-- doc -/\n\ndef inc := 1\n")
        assert minified is not None
        assert minified.lines == ("/-- doc -/", "def inc := 1")
        assert minified.source_lines == (1, 3)


class TestFallback:
    def test_unterminated_string_returns_none(self) -> None:
        assert minify_lines('foo := "open -- never closed') is None

    def test_unterminated_block_comment_returns_none(self) -> None:
        assert minify_lines("foo\n/- never closed -- dangle\n") is None

    def test_unterminated_docstring_returns_none(self) -> None:
        assert minify_lines("/-- dangling docstring\ntheorem t : True\n") is None

    def test_unterminated_char_literal_returns_none(self) -> None:
        assert minify_lines("c := 'q -- no close") is None


class TestLineAccounting:
    def test_source_lines_track_surviving_lines_exactly(self) -> None:
        source = (
            "/-! header -/\n"                      # 1
            "\n"                                    # 2
            "theorem t : True := trivial -- ok\n"   # 3
            "\n"                                    # 4
            "theorem u : False := by\n"             # 5
            "  exact absurd trivial\n"              # 6
            "-- trailing comment\n"                 # 7
        )
        minified = minify_lines(source)
        assert minified is not None
        assert minified.lines == (
            "theorem t : True := trivial",
            "theorem u : False := by",
            "  exact absurd trivial",
        )
        assert minified.source_lines == (3, 5, 6)
