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

- redundant horizontal whitespace: runs of spaces/tabs collapse to a
  single space between tokens; leading structural indentation is
  preserved.

What is kept: everything else — indentation stays put. Declaration
docstrings (`/-- ... -/`) are stripped like any other comment.

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
MINIFIER_VERSION = 4


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
    text: list[str] = []  # characters of the line being built
    current = 1  # source line the line being built started on
    current_leading = ""  # leading horizontal whitespace of the line
    at_line_start = True
    in_string = False
    string_escape = False
    depth = 0  # nesting of the block comment being stripped
    comment_open_leading = ""
    comment_prev_nonspace = False
    comment_had_newline = False
    continuation_pending = False
    just_consumed_char = False

    def emit() -> None:
        nonlocal continuation_pending
        if continuation_pending:
            joined = "".join(text)
            cur = joined[: len(joined) - len(joined.lstrip(" \t"))] if joined else ""
            if len(cur) < len(comment_open_leading):
                text[:] = list(comment_open_leading) + text[len(cur) :]
        lines.append("".join(text))
        numbers.append(current)
        continuation_pending = False

    i = 0
    n = len(source)
    while i < n:
        c = source[i]
        prev_consumed_char = just_consumed_char
        just_consumed_char = False

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
            at_line_start = False
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
                was_depth = depth
                depth -= 1
                i += 2
                if was_depth == 1 and depth == 0:
                    # Comment closed.
                    if comment_had_newline:
                        # Preserve the opening line's leading indentation on
                        # the continuation line that closes this comment.
                        continuation_pending = True
                        current_leading = comment_open_leading
                        at_line_start = True
                    else:
                        # Single-line inline comment: insert a separating
                        # space when flanked by non-whitespace on the same
                        # line, so adjacent tokens do not merge.
                        if comment_prev_nonspace and i < n and source[i] not in " \t\n":
                            if not text or not text[-1].isspace():
                                text.append(" ")
                continue
            if c == "\n":
                emit()
                text = []
                current_leading = ""
                at_line_start = True
                comment_had_newline = True
                current += 1
            i += 1
            continue

        if source.startswith("/-", i):
            comment_prev_nonspace = bool(text) and text[-1].strip() != ""
            comment_open_leading = current_leading
            comment_had_newline = False
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
            at_line_start = False
            i += 1
            continue

        if c == "'" and not (
            i > 0
            and (source[i - 1].isalnum() or source[i - 1] in "_'")
            and not prev_consumed_char
        ):
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
            at_line_start = False
            just_consumed_char = True
            i = j
            continue

        if c == "\n":
            emit()
            text = []
            current_leading = ""
            at_line_start = True
            current += 1
            i += 1
            continue

        if c in " \t":
            if at_line_start:
                text.append(c)
                current_leading += c
            else:
                if text and text[-1] in " \t":
                    # Collapse runs of horizontal whitespace to a single
                    # space between tokens.
                    text[-1] = " "
                else:
                    text.append(c)
            i += 1
            continue

        text.append(c)
        at_line_start = False
        i += 1
        continue

    if in_string or depth:
        return None
    if text:
        emit()

    out_lines: list[str] = []
    out_numbers: list[int] = []
    for line, number in zip(lines, numbers):
        stripped_line = line.rstrip()
        if not stripped_line:
            continue  # blank lines are pure layout
        out_lines.append(stripped_line)
        out_numbers.append(number)
    return Minified(tuple(out_lines), tuple(out_numbers))
