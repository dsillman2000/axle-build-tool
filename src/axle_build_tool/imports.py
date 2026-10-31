"""Parsing of Lean 4 `import` statements.

A pure, line-oriented parser: given the text of a `.lean` file it returns
the module names that file imports, e.g. `["Divisibility", "EuclidLemma"]`.
Resolution of import names to project files happens in the manifest
engine, not here.
"""

from __future__ import annotations

import re

#: A single Lean import line: `import Foo`, `import Foo.Bar.Baz`.
_IMPORT_LINE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$")


def strip_comments(source: str) -> str:
    """Remove `--` and `/- -/` comments while preserving line structure.

    Block comments may be nested. Line breaks inside comments are kept so
    that callers can keep matching line by line. Shared line-oriented
    preprocessing for axbt's local parsers.
    """
    out: list[str] = []
    depth = 0
    i = 0
    length = len(source)
    while i < length:
        if depth > 0:
            if source.startswith("-/", i):
                depth -= 1
                i += 2
            elif source.startswith("/-", i):
                depth += 1
                i += 2
            elif source[i] == "\n":
                out.append("\n")
                i += 1
            else:
                i += 1
        elif source.startswith("--", i):
            while i < length and source[i] != "\n":
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            i += 2
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def parse_imports(source: str) -> list[str]:
    """Return the module names imported at the top of a Lean source file.

    Imports must precede all declarations in a Lean file, so scanning
    stops at the first line that is neither blank, a comment, nor an
    import.
    """
    imports: list[str] = []
    for line in strip_comments(source).splitlines():
        if not line.strip():
            continue
        match = _IMPORT_LINE.match(line)
        if match:
            imports.append(match.group(1))
        elif line.strip() == "prelude":
            continue  # `prelude` may precede the imports of a core-style file
        else:
            break
    return imports
