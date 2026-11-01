"""Standalone payload assembly for files and selections.

Files that reference other project files cannot be evaluated standalone
by the Axle API, so every submission uses an *isolated payload*: the
selected files' full transitive dependency sources inlined in topological
order (dependencies first — Lean files are order-sensitive), with all
import lines hoisted into a single deduplicated header block (Lean only
allows imports at the beginning of a file; intra-project imports are
replaced by the inlined content).

Payloads are persisted under `.axbt/compiled/` so the exact code sent to
the Axle API is inspectable ("Inspection Support" of compile's
incremental plan).
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from axle_build_tool.config import CACHE_DIRNAME
from axle_build_tool.manifest import Manifest, ManifestNode
from axle_build_tool.stubbing import PROOF_KINDS, stubbed_source

_IMPORT_LINE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*(?:--.*)?$")

#: Subdirectory of the cache holding persisted payloads.
COMPILED_DIRNAME = "compiled"


@dataclass
class Payload:
    """A standalone payload covering one or more manifest nodes."""

    content: str
    #: The payload's lines (same content split into lines).
    lines: list[str]
    #: Node name -> 1-based inclusive line span of its section.
    sections: dict[str, tuple[int, int]]
    #: Node name -> source line number of each of the section's lines
    #: (parallel to the section's slice of `lines`). Import lines have no
    #: counterpart in the payload, so the mapping skips them; this is the
    #: exact, order-independent way to attribute payload positions back
    #: to the original files.
    line_map: dict[str, list[int]]


def dotted_stem_of(node: ManifestNode) -> str:
    """The dotted file stem of a node: `Utils/Basic.lean` -> `Utils.Basic`."""
    return node.name[len(node.module) + 1:]


def build_payload(
    nodes: Sequence[ManifestNode],
    manifest: Manifest,
    project_root: Path,
    stubbed: dict[str, frozenset[str] | None] | None = None,
    warnings: list[str] | None = None,
) -> Payload:
    """Assemble a standalone payload covering `nodes` plus their full
    transitive dependency closure.

    The dependency closure is visited parents-first (the manifest DAG is
    acyclic and already validated), then the selected nodes follow in
    name order. Every node's section span is recorded, along with the
    source line each section line came from (`line_map`), so callers can
    attribute extracted documents or diagnostics back to a file.

    `stubbed` (the `--sorry` machinery) maps node names to the
    declarations to stub in that node — `None` meaning every stubbable
    declaration. A stubbed node's section is built from its
    stubbed source; line maps still refer to the *original* file
    (stub lines have no counterpart there).
    """
    by_name = manifest.by_name()
    order: list[ManifestNode] = []
    seen: set[str] = set()

    def visit(current: ManifestNode) -> None:
        if current.name in seen:
            return
        seen.add(current.name)
        for parent_name in sorted(current.parents):
            visit(by_name[parent_name])
        order.append(current)

    for node in sorted(nodes, key=lambda n: n.name):
        visit(node)

    hoisted: list[str] = []
    hoisted_seen: set[str] = set()
    sections: list[tuple[ManifestNode, list[str], list[int]]] = []
    for member in order:
        source = (project_root / member.path).read_text(encoding="utf-8")
        if stubbed and member.name in stubbed:
            source = stubbed_source(
                member, source, stubbed[member.name], warnings=warnings
            )
        internal_stems = {
            dotted_stem_of(by_name[parent_name]) for parent_name in member.parents
        }
        section: list[str] = []
        line_numbers: list[int] = []
        for number, line in enumerate(source.splitlines(), start=1):
            match = _IMPORT_LINE.match(line)
            if match is None:
                section.append(line)
                line_numbers.append(number)
                continue
            # Every import line leaves the section: intra-project imports
            # are satisfied by the inlined content; external ones are
            # hoisted into the payload's single header block.
            if match.group(1) not in internal_stems and match.group(1) not in hoisted_seen:
                hoisted_seen.add(match.group(1))
                hoisted.append(line)
        sections.append((member, section, line_numbers))

    lines: list[str] = []
    if hoisted:
        lines.extend(hoisted)
        lines.append("")
    result = Payload(content="", lines=[], sections={}, line_map={})
    for index, (member, section, line_numbers) in enumerate(sections):
        if index:
            lines.append("")
        start = len(lines) + 1
        lines.extend(section)
        result.sections[member.name] = (start, len(lines))
        result.line_map[member.name] = line_numbers
    result.lines = lines
    result.content = "\n".join(lines) + "\n"
    return result


def source_position(payload: Payload, line: int) -> tuple[str, int] | None:
    """Map a 1-based payload line to (node name, source file line).

    Returns `None` for lines outside every node's section (the hoisted
    import header block, or out-of-range lines).
    """
    for node_name, (start, end) in payload.sections.items():
        if start <= line <= end:
            return node_name, payload.line_map[node_name][line - start]
    return None


def build_file_payload(
    node: ManifestNode,
    manifest: Manifest,
    project_root: Path,
    *,
    stub_dependencies: bool = False,
) -> Payload:
    """A payload for a single node (the per-file form of `build_payload`).

    With `stub_dependencies=True`, every *other* node's **proof bodies**
    (theorem/lemma/example) are stubbed down to `:= by sorry` — the `--sorry`
    machinery, applied in reverse — while the dependencies' definitions,
    abbrevs, instances, and structures stay real (downstream elaboration
    unfolds and projects on them, so erasing those breaks compilation, as
    observed with type abbrevs like `CombVertex` and Prop-valued defs like
    `IsMassDist`). Extraction only consumes the selected node's own spans
    and signatures — dependency documents are dropped — and skipping the
    dependencies' proof elaboration is where extraction's cost lives for
    large closures. Used by `apply_extraction`; check/verify still build
    full payloads.
    """
    stubbed: dict[str, frozenset[str] | None] | None = None
    if stub_dependencies:
        stubbed = {}
        for other in manifest.nodes:
            if other.name == node.name:
                continue
            proofs = frozenset(
                declaration.name
                for declaration in other.declarations
                if declaration.kind in PROOF_KINDS
            )
            if proofs:
                stubbed[other.name] = proofs
    return build_payload([node], manifest, project_root, stubbed=stubbed)


def compiled_payload_dir(project_root: Path) -> Path:
    """The `.axbt/compiled/` directory of `project_root`."""
    return project_root / CACHE_DIRNAME / COMPILED_DIRNAME


def compiled_filename(
    module: str, stem: str | None = None, variant: str = "isolated"
) -> str:
    """The persisted payload filename for a module- or file-level selection.

    Dots in dotted stems become underscores; `variant` selects the
    payload kind (`isolated` for compiled payloads, `stubbed` for
    `--sorry` submissions):
    `compiled_filename("M", "Utils.Basic")` -> `M_Utils_Basic_isolated.lean`.
    """
    base = module if stem is None else f"{module}_{stem.replace('.', '_')}"
    return f"{base}_{variant}.lean"


def write_compiled_payloads(manifest: Manifest, project_root: Path) -> list[Path]:
    """Persist per-file isolated payloads under `.axbt/compiled/`.

    Returns the written paths, in manifest (name-sorted) order.
    """
    out_dir = compiled_payload_dir(project_root)
    out_dir.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    for node in manifest.nodes:
        payload = build_payload([node], manifest, project_root)
        path = out_dir / compiled_filename(node.module, dotted_stem_of(node))
        path.write_text(payload.content, encoding="utf-8")
        written.append(path)
    return written
