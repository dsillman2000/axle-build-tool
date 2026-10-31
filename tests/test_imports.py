"""Unit tests for the Lean import parser."""

from __future__ import annotations

from pathlib import Path

from axle_build_tool.imports import parse_imports


class TestParseImports:
    def test_dotted_import_is_a_single_name(self) -> None:
        assert parse_imports("import Init.System.IO\n") == ["Init.System.IO"]

    def test_no_imports(self) -> None:
        assert parse_imports("theorem t : True := True.intro\n") == []

    def test_commented_out_import_is_ignored(self) -> None:
        assert parse_imports("-- import Foo\ndef x := 1\n") == []
        assert parse_imports("--import Foo\n") == []

    def test_import_with_trailing_comment(self) -> None:
        assert parse_imports("import Foo -- why not\n") == ["Foo"]

    def test_imports_inside_block_comment_are_ignored(self) -> None:
        source = "/-!\nimport Fake\n-/\nimport Real\n"
        assert parse_imports(source) == ["Real"]

    def test_nested_block_comments(self) -> None:
        source = "/- outer /- inner import Fake -/ still commented -/\nimport Real\n"
        assert parse_imports(source) == ["Real"]

    def test_scanning_stops_at_first_declaration(self) -> None:
        assert parse_imports("def x := 1\nimport Fake\n") == []

    def test_prelude_may_precede_imports(self) -> None:
        assert parse_imports("prelude\nimport Init\n") == ["Init"]

    def test_multiple_imports_in_order(self) -> None:
        source = "import Aa\nimport Bb.Cc\nimport Dd\n\ndef x := 1\n"
        assert parse_imports(source) == ["Aa", "Bb.Cc", "Dd"]
