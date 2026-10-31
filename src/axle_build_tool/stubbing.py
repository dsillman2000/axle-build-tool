"""Stubbing of declaration bodies for isolated payloads (plan §5).

Passing `--sorry <selector>` trades upstream completeness for speed:
the selected dependency subtree's proof and definition bodies are
replaced with `sorry` stubs, keeping every signature intact, so
downstream code still elaborates against the stubbed declarations'
types without paying for their (possibly slow or broken) proofs.

Stubbing is **local span replacement**: each stubbed declaration's
recorded line span (exact file coordinates from extraction) is
replaced by a single stub line built from its extracted signature.
The replacement happens inside the file's own text, so the enclosing
`namespace`/`section`/`variable`/`open` context survives by
construction — no code is moved out of its scope.

Which kinds are stubbed:

- `theorem` / `lemma` / `example` — proof bodies become `:= by sorry`.
- `def` / `abbrev` — definition bodies become `:= sorry`.
- `structure` / `class` / `inductive` / `instance` (and anything else)
  stay real: their bodies are structural (constructors, instances),
  not proofs, and removing them would break downstream elaboration.

A declaration's extracted signature may carry its docstring (observed:
multi-line docstrings are prepended to the signature text). The stub
keeps the *statement* only — the original docstring lines sit above
the replaced span and re-attach to the stub naturally.

Limitation: spans come from the manifest, so a source edited after a
compile (the `--no-compile` path) can make them misaligned; spans that
fall outside the current source are skipped defensively.
"""

from __future__ import annotations

import re

from axle_build_tool.manifest import ExtractedDecl, ManifestNode

#: Kinds whose bodies are proofs — stubbed with `:= by sorry`.
PROOF_KINDS = frozenset({"theorem", "lemma", "example"})
#: Kinds with a stubbable body — proof kinds plus definitional kinds.
STUBBABLE_KINDS = PROOF_KINDS | {"def", "abbrev"}


def _statement_of(signature: str) -> str:
    """The signature without a leading docstring, if it carries one.

    Docstrings appear when extraction prepends them to the signature
    (observed with multi-line docstrings); the statement starts after
    the last docstring close. Signatures without a docstring are
    returned unchanged.
    """
    close = signature.rfind("-/")
    if close != -1 and "/--" in signature[: close + 2]:
        return signature[close + 2:].strip()
    return signature.strip()


def _stub_line(declaration: ExtractedDecl) -> str:
    statement = _statement_of(declaration.signature)
    separator = " := by sorry" if declaration.kind in PROOF_KINDS else " := sorry"
    return f"{statement}{separator}"


def stubbed_source(
    node: ManifestNode,
    source: str,
    only: frozenset[str] | None = None,
) -> str:
    """`source` with the node's stubbable declarations replaced by stubs.

    `only` restricts stubbing to those declaration names; by default
    every stubbable declaration (`STUBBABLE_KINDS`) in the node is
    stubbed. Spans that overlap, are inverted, or fall outside the
    current source are left in place (defensive against stale
    manifests).
    """
    lines = source.splitlines()
    out: list[str] = []
    cursor = 0  # 0-based index of the next unconsumed line

    for declaration in sorted(node.declarations, key=lambda d: d.line_pos):
        if declaration.kind not in STUBBABLE_KINDS:
            continue
        if only is not None and declaration.name not in only:
            continue
        start = declaration.line_pos - 1
        end = declaration.end_line_pos  # exclusive slice bound
        if start < cursor or start >= end or end > len(lines):
            continue
        out.extend(lines[cursor:start])
        out.append(_stub_line(declaration))
        cursor = end

    out.extend(lines[cursor:])
    return "\n".join(out) + ("\n" if lines else "")
