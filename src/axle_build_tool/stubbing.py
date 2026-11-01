"""Stubbing of declaration bodies for isolated payloads (`--sorry`).

Passing `--sorry <selector>` trades upstream completeness for speed:
the selected dependency subtree's proof bodies are replaced with
`sorry` stubs, keeping every signature intact, so downstream code still
elaborates against the stubbed declarations' types without paying for
their (possibly slow or broken) proofs.

Stubbing is **local span replacement**: each stubbed declaration's
recorded line span (exact file coordinates from extraction) is
replaced by a single stub line built from its extracted signature.
The replacement happens inside the file's own text, so the enclosing
`namespace`/`section`/`variable`/`open` context survives by
construction — no code is moved out of its scope.

Which kinds are stubbed:

- `theorem` / `lemma` / `example` — proof bodies become `:= by sorry`.
- everything else — `def`, `abbrev`, `structure` / `class` /
  `inductive` / `instance`, and any other kind — stays real.

Definitional bodies are kept deliberately: a def's body is content,
not proof. Downstream proofs routinely unfold it (anonymous
constructors against the type, projections, `rfl`), so replacing a
body with `sorry` makes the declaration opaque and breaks exactly the
elaboration the stubs were meant to leave working. A granted def or
abbrev keeps its body and still counts as granted (excused) — which
also covers the placeholder case of a def whose source body is a
`sorry`.

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
#: Kinds a `--sorry` grant covers: proof kinds get stubbed bodies; def
#: and abbrev keep their real bodies (they are unfolded definitionally
#: downstream) but count as granted — excused from verify's sweep.
GRANTED_KINDS = PROOF_KINDS | {"def", "abbrev"}


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


def _span_head_matches(line: str, kind: str) -> bool:
    """Whether a span's first line looks like the declaration's keyword line.

    Extraction snaps `line_pos` onto the declaration's keyword line, so a
    healthy span starts there (or, in the rare snap-fallback case, on the
    declaration's docstring). Anything else means the manifest is out of
    date with the source.
    """
    stripped = line.lstrip()
    return stripped.startswith(kind) or stripped.startswith("/-")


#: The declaration keywords a signature can start (after modifiers).
_KIND_TOKENS = frozenset(
    {"theorem", "lemma", "example", "def", "abbrev", "structure", "class", "inductive", "instance"}
)


def bare_name(declaration: ExtractedDecl) -> str:
    """The declaration's name as written in its file.

    Extraction records the Lean-qualified name (`Scoped.variable_holds`
    for a declaration inside `namespace Scoped`), while the signature is
    the in-file text — so the name token after the kind keyword is the
    bare name. Anonymous declarations (e.g. nameless `instance`s) have
    none; they fall back to the last segment of the qualified name.
    """
    statement = _statement_of(declaration.signature)
    tokens = statement.replace(":", " : ").split()
    for index, token in enumerate(tokens):
        if token in _KIND_TOKENS and index + 1 < len(tokens):
            candidate = tokens[index + 1]
            if not candidate.startswith((":", "(", "[", "{", "`")):
                return candidate
            break
    return declaration.name.rsplit(".", 1)[-1]


def stubbed_source(
    node: ManifestNode,
    source: str,
    only: frozenset[str] | None = None,
    warnings: list[str] | None = None,
) -> str:
    """`source` with the node's granted proof declarations replaced by stubs.

    `only` restricts stubbing to those declaration names; by default
    every proof declaration (`PROOF_KINDS`) in the node is stubbed —
    def/abbrev grants keep their real bodies. Spans that overlap, are
    inverted, fall outside the current source, or don't start where the
    declaration's keyword should be are left in place (defensive
    against stale manifests) — when `warnings` is given, each skip
    appends a message there naming the file and the prescription.
    """
    lines = source.splitlines()
    out: list[str] = []
    cursor = 0  # 0-based index of the next unconsumed line

    for declaration in sorted(node.declarations, key=lambda d: d.line_pos):
        if declaration.kind not in PROOF_KINDS:
            continue
        if only is not None and declaration.name not in only:
            continue
        start = declaration.line_pos - 1
        end = declaration.end_line_pos  # exclusive slice bound
        stale = (
            start < cursor
            or start >= end
            or end > len(lines)
            or not _span_head_matches(lines[start], declaration.kind)
        )
        if stale:
            if warnings is not None:
                warnings.append(
                    f"{node.path}: declaration '{declaration.name}' could not be "
                    "stubbed (the manifest is out of date with the source); "
                    "run `axbt compile` to rebuild it."
                )
            continue
        out.extend(lines[cursor:start])
        out.append(_stub_line(declaration))
        cursor = end

    out.extend(lines[cursor:])
    return "\n".join(out) + ("\n" if lines else "")
