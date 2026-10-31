"""Parsing of Lean 4 scope structure: `namespace`/`section`/`variable`/`open`.

A pure, line-oriented scanner — the same philosophy as `parse_imports`:
local parsing owns file *structure*, the Axle API owns declaration
*semantics*. Given the text of a `.lean` file it maps every line to the
scope active at that point: the ordered list of scope-affecting header
lines in effect there — `namespace` and `section` opens in nesting
order, followed by the `variable` and `open` lines in encounter order.

Consumers (the isolation engine) reconstruct scope preambles from these
headers: re-emitting `preamble_at(line)` above a declaration's signature
reproduces the declaration's original scope for standalone elaboration,
and in-place stubbing can trust that a span replaced inside the file
stays inside its original scope context.

Scope semantics encoded here:

- `namespace Foo` (dotted names allowed) and `section [name]` push a
  scope; a matching `end [name]` pops the innermost one.
- `variable` lines accumulate while their enclosing scope is open; a
  re-declared variable appears twice (the later line shadows the
  earlier, matching Lean's semantics).
- `open Foo`, `open Foo Bar`, `open Foo hiding ...`, `open Foo renaming
  ...`, and `open scoped Foo` are active until their scope closes.
- `open ... in <command>` is **transient**: it applies to the command
  it annotates only — either on the same line or (when the `in` ends
  the line) the next content line. It never outlives that command.

Known limitations of the line-oriented approach (accepted, as in
`parse_imports`): each command is assumed to occupy a single line, and
string literals are not tracked (a scope-shaped line inside a multiline
string would be misread). Scope keywords inside comments — line,
block, nested block, and docstrings — are ignored. Other command-scoped
forms (`set_option ... in`, attributes, `universe`) are not scopes and
are not tracked.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Literal

from axle_build_tool.imports import strip_comments

ScopeKind = Literal["namespace", "section", "variable", "open", "end"]

_NAMESPACE = re.compile(r"^namespace\s+(\S+)$")
_SECTION = re.compile(r"^section(?:\s+(\S+))?$")
_END = re.compile(r"^end(?:\s+\S+)?$")
_VARIABLE = re.compile(r"^variable\b")
_OPEN = re.compile(r"^open\b")
#: The `in` that terminates a transient `open ... in <command>` line.
_IN_SEPARATOR = re.compile(r"\bin\b")


@dataclass(frozen=True)
class ScopeHeader:
    """One scope-affecting header line, in file coordinates."""

    #: 1-based file line of the header.
    line: int
    kind: ScopeKind
    #: The header's source line, trimmed. Transient `open ... in`
    #: headers record the open clause only (without the trailing `in`).
    text: str
    #: True for `open ... in` headers, which apply to the command they
    #: annotate only, never to subsequent declarations.
    transient: bool = False


@dataclass(frozen=True)
class ScopeMap:
    """Maps each line of a Lean source file to its active scope."""

    #: 1-based line -> the active headers at that line, in document order.
    snapshots: dict[int, tuple[ScopeHeader, ...]]

    def at(self, line: int) -> tuple[ScopeHeader, ...]:
        """The scope headers active at 1-based `line` (document order).

        Lines outside the file resolve to no scope.
        """
        return self.snapshots.get(line, ())

    def preamble_at(self, line: int) -> str:
        """Reconstruct the scope preamble at 1-based `line` as Lean source.

        The active headers' texts in document order — re-emitting the
        result above a declaration reproduces the declaration's original
        scope context in a standalone file.
        """
        return "\n".join(header.text for header in self.at(line))


def _match_header(line: str, number: int) -> tuple[ScopeHeader, bool] | None:
    """Classify a (comment-stripped, trimmed) line as a scope header.

    Returns the header and whether its command shares the line (only
    the transient `open ... in <command>` form can).
    """
    if _NAMESPACE.match(line):
        return ScopeHeader(number, "namespace", line), False
    if _SECTION.match(line):
        return ScopeHeader(number, "section", line), False
    if _END.match(line):
        return ScopeHeader(number, "end", line), False
    if _VARIABLE.match(line):
        return ScopeHeader(number, "variable", line), False
    if _OPEN.match(line):
        parts = _IN_SEPARATOR.split(line, maxsplit=1)
        if len(parts) == 2:
            # Both transient forms record the bare open clause (without
            # the trailing `in`), so preambles reconstruct valid Lean.
            return ScopeHeader(number, "open", parts[0].strip(), transient=True), (
                bool(parts[1].strip())
            )
        return ScopeHeader(number, "open", line), False
    return None


def parse_scopes(source: str) -> ScopeMap:
    """Map every line of `source` to its active scope.

    Every line receives a snapshot of the headers active at that
    point. A transient `open ... in` header is active from its own line
    through the line of the command it annotates — blank and comment
    lines in between do not consume it — and never beyond. Chained
    transient opens (`open Foo in` / `open Bar in` / `def ...`) all
    apply to the command.
    """
    snapshots: dict[int, tuple[ScopeHeader, ...]] = {}
    active: list[ScopeHeader] = []
    #: Indices into `active` where each open namespace/section block
    #: starts; an `end` truncates the block (its header and every
    #: variable/open inside it) in one step.
    block_starts: list[int] = []
    pending: list[ScopeHeader] = []

    for number, raw in enumerate(strip_comments(source).splitlines(), start=1):
        line = raw.strip()

        if not line:
            # Blank or comment-only: no transient open applies yet.
            snapshots[number] = tuple(active)
            continue

        matched = _match_header(line, number)
        if matched is None:
            # A content line: every pending transient open applies here.
            snapshots[number] = tuple(active) + tuple(pending)
            pending.clear()
            continue

        header, inline_command = matched
        if header.kind == "end":
            # The scope is still active at the `end` line itself.
            snapshots[number] = tuple(active)
            if block_starts:
                del active[block_starts.pop():]
            continue

        if header.transient:
            pending.append(header)
            snapshots[number] = tuple(active) + tuple(pending)
            if inline_command:
                # `open Foo in <command>` on one line: consumed at once.
                pending.clear()
            continue

        if header.kind in ("namespace", "section"):
            block_starts.append(len(active))
        active.append(header)
        snapshots[number] = tuple(active)

    return ScopeMap(snapshots=snapshots)
