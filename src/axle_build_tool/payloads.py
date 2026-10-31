"""Standalone payload assembly for files and selections.

Files that reference other project files cannot be evaluated standalone
by the Axle API, so every submission uses an *isolated payload*: the
selected files' full transitive dependency sources inlined in topological
order (dependencies first — Lean files are order-sensitive), with all
import lines hoisted into a single deduplicated header block (Lean only
allows imports at the beginning of a file; intra-project imports are
replaced by the inlined content).

Payloads are persisted under `.axbt/compiled/` so the exact code sent to
the Axle API is inspectable (plan §3, "Inspection Support").
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from axle_build_tool.config import CACHE_DIRNAME
from axle_build_tool.manifest import Manifest, ManifestNode

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
    #: Node name -> number of import lines removed from its section.
    stripped: dict[str, int]


def dotted_stem_of(node: ManifestNode) -> str:
    """The dotted file stem of a node: `Utils/Basic.lean` -> `Utils.Basic`."""
    return node.name[len(node.module) + 1:]


def build_payload(
    nodes: Sequence[ManifestNode],
    manifest: Manifest,
    project_root: Path,
) -> Payload:
    """Assemble a standalone payload covering `nodes` plus their full
    transitive dependency closure.

    The dependency closure is visited parents-first (the manifest DAG is
    acyclic and already validated), then the selected nodes follow in
    name order. Every node's section span is recorded so callers can
    attribute extracted documents or errors back to a file.
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
    sections: list[tuple[ManifestNode, list[str], int]] = []
    for member in order:
        source = (project_root / member.path).read_text(encoding="utf-8")
        internal_stems = {
            dotted_stem_of(by_name[parent_name]) for parent_name in member.parents
        }
        section: list[str] = []
        stripped = 0
        for line in source.splitlines():
            match = _IMPORT_LINE.match(line)
            if match is None:
                section.append(line)
                continue
            # Every import line leaves the section: intra-project imports
            # are satisfied by the inlined content; external ones are
            # hoisted into the payload's single header block.
            stripped += 1
            if match.group(1) not in internal_stems and match.group(1) not in hoisted_seen:
                hoisted_seen.add(match.group(1))
                hoisted.append(line)
        sections.append((member, section, stripped))

    lines: list[str] = []
    if hoisted:
        lines.extend(hoisted)
        lines.append("")
    result = Payload(content="", lines=[], sections={}, stripped={})
    for index, (member, section, stripped) in enumerate(sections):
        if index:
            lines.append("")
        start = len(lines) + 1
        lines.extend(section)
        result.sections[member.name] = (start, len(lines))
        result.stripped[member.name] = stripped
    result.lines = lines
    result.content = "\n".join(lines) + "\n"
    return result


def build_file_payload(
    node: ManifestNode,
    manifest: Manifest,
    project_root: Path,
) -> Payload:
    """A payload for a single node (the per-file form of `build_payload`)."""
    return build_payload([node], manifest, project_root)


def compiled_payload_dir(project_root: Path) -> Path:
    """The `.axbt/compiled/` directory of `project_root`."""
    return project_root / CACHE_DIRNAME / COMPILED_DIRNAME


def compiled_filename(module: str, stem: str | None = None) -> str:
    """The persisted payload filename for a module- or file-level selection.

    Dots in dotted stems become underscores:
    `compiled_filename("M", "Utils.Basic")` -> `M_Utils_Basic_isolated.lean`.
    """
    base = module if stem is None else f"{module}_{stem.replace('.', '_')}"
    return f"{base}_isolated.lean"


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
