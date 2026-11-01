"""Best-effort Lean source minification for submitted payloads.

Payload submissions carry the dependency closure's full source text —
comments, section headers, blank-line runs included. None of that is
proof content, and stripping it shrinks the request bodies and the
persisted `.axbt/compiled/` artifacts. Minification runs at payload
assembly, *after* `--sorry` stubbing (manifest spans are keyed to raw
source), and reports which original source line each surviving line
came from, so the payload line maps keep attributing API diagnostics
back to files exactly.

What is stripped:

- line comments (`-- ...`) and block comments (`/- ... -/`, including
  the `/-! ... -/` section-header form), with nesting honored;
- runs of blank lines (blank lines are pure layout) and trailing
  whitespace on every surviving line.

What is kept: everything else — indentation stays put, and declaration
docstrings (`/-- ... -/`) survive verbatim, since they attach to
declarations and may feed the API's declaration tooling.

The scan is a small state machine: string literals are tracked (a `--`
or `/-` inside a string is text, not a comment), and char literals are
consumed wholesale so a raw quote inside (`'"'`) cannot be mistaken for
a string boundary; identifier-tailed apostrophes (`x'`) are plain
characters. Newlines inside comments still advance the line accounting,
so comment removal never joins lines — attribution stays exact.

Best-effort discipline: when the text does not track cleanly (an
unterminated string or comment at end of input), `minify_lines` returns
`None` and callers submit the original text. Minification must never
turn a would-pass submission into a failure.

Known, accepted limitation: interpolated strings (`s!"…{…}…"`) with
embedded string literals are not tracked as one unit, so comment
sequences inside an interpolated quote could be misjudged on such a
line. This does not occur in typical proof content.
"""

from __future__ import annotations

from dataclasses import dataclass

#: Version of the minifier's output. It rides in the closure-signature
#: options material (via `signature_marker`), so a behavior change here
#: invalidates stamps and the verify cache exactly once, instead of
#: silently covering submissions shaped differently.
MINIFIER_VERSION = 1


def signature_marker(enabled: bool) -> str:
    """The minify part of the closure-signature options material."""
    return f"on@v{MINIFIER_VERSION}" if enabled else "off"


@dataclass(frozen=True)
class Minified:
    """Minified source lines, each tagged with its original line number.

    `source_lines[i]` is the 1-based source line `lines[i]` came from;
    parallel by construction. Stubs already replaced by the caller keep
    the numbering of the text handed in (they have no raw-source
    counterpart, matching the unminified behavior).
    """

    lines: tuple[str, ...]
    source_lines: tuple[int, ...]


#: Characters an identifier may continue with — an apostrophe right
#: after these is an identifier tail (`x'`), not a char literal.
_IDENT_CHARS = frozenset(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'"
)


def minify_lines(source: str) -> Minified | None:
    """`source` stripped of comments and blank lines (`None` = don't).

    Returns the surviving lines in order, each tagged with the 1-based
    source line it came from; `None` when the input does not track
    cleanly (unterminated string, char literal, or comment) so callers
    can fall back to the original text.
    """
    if not source:
        return Minified((), ())

    lines: list[str] = []
    numbers: list[int] = []
    kept_flags: list[bool] = []  # per line: emitted inside a kept docstring
    text: list[str] = []  # characters of the line being built
    current = 1  # source line the line being built started on
    last: str | None = None  # last content character appended
    in_string = False
    string_escape = False
    depth = 0  # nesting of the block comment being stripped
    keep_depth = 0  # nesting of the docstring being preserved

    def emit(kept: bool = False) -> None:
        lines.append("".join(text))
        numbers.append(current)
        kept_flags.append(kept)

    i = 0
    n = len(source)
    while i < n:
        c = source[i]

        if in_string:
            if string_escape:
                string_escape = False
            elif c == "\\":
                string_escape = True
            elif c == '"':
                in_string = False
            elif c == "\n":
                return None  # Lean strings are single-line
            text.append(c)
            last = c
            i += 1
            continue

        if keep_depth:
            # Inside a preserved `/-- ... -/` docstring: copy verbatim,
            # tracking `/-` nesting only for the matching close.
            if source.startswith("/-", i):
                keep_depth += 1
                text.append("/-")
                last = "-"
                i += 2
                continue
            if source.startswith("-/", i):
                keep_depth -= 1
                text.append("-/")
                last = "/"
                i += 2
                continue
            if c == "\n":
                emit(kept=True)
                text = []
                current += 1
                i += 1
                continue
            text.append(c)
            last = c
            i += 1
            continue

        if depth:
            # Inside a block comment being stripped; newlines inside it
            # still advance the line accounting (never join lines).
            if source.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if source.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            if c == "\n":
                emit()
                text = []
                current += 1
            i += 1
            continue

        if source.startswith("/-", i):
            if i + 2 < n and source[i + 2] == "-":
                # `/-` immediately followed by `-` (`/-- … -/`): a
                # declaration docstring — preserve it verbatim.
                keep_depth = 1
                text.append("/-")
                last = "-"
                i += 2
                continue
            depth = 1
            i += 2
            continue

        if source.startswith("--", i):
            # Line comment: skip to end of line; the newline itself is
            # handled normally on the next iteration.
            i += 2
            while i < n and source[i] != "\n":
                i += 1
            continue

        if c == '"':
            in_string = True
            string_escape = False
            text.append(c)
            last = c
            i += 1
            continue

        if c == "'" and (last is None or last not in _IDENT_CHARS):
            # Char literal (`'"'`, `'-\''`): consume the whole literal
            # without interpreting it, so a raw quote inside cannot be
            # mistaken for a string boundary.
            j = i + 1
            closed = False
            while j < n:
                scan = source[j]
                if scan == "\\":
                    j += 2
                    continue
                if scan == "\n":
                    break
                if scan == "'":
                    closed = True
                    j += 1
                    break
                j += 1
            if not closed:
                return None
            text.append(source[i:j])
            last = "'"
            i = j
            continue

        if c == "\n":
            emit()
            text = []
            current += 1
            i += 1
            continue

        text.append(c)
        last = c
        i += 1

    if in_string or depth or keep_depth:
        return None
    out_lines: list[str] = []
    out_numbers: list[int] = []
    for line, number, was_kept in zip(lines, numbers, kept_flags):
        if was_kept:
            # Docstring prose is verbatim, blank lines included.
            out_lines.append(line)
            out_numbers.append(number)
            continue
        stripped_line = line.rstrip()
        if not stripped_line:
            continue  # blank lines are pure layout
        out_lines.append(stripped_line)
        out_numbers.append(number)
    return Minified(tuple(out_lines), tuple(out_numbers))
