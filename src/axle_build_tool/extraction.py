"""Applying Axle declaration extraction to manifest nodes.

Files that use intra-project imports cannot be evaluated standalone by
the Axle API (their project references would not resolve), so
`apply_extraction` submits an *isolated payload* per node instead: the
node's transitive dependencies inlined in topological order, followed by
the node's own source, with intra-project import lines stripped
throughout (they are replaced by the inlined content; external imports
such as `import Mathlib` are kept).

Extracted declarations are attributed back to the node's own file by
line-span and shifted back into original-file coordinates; documents
belonging to inlined dependencies are dropped (they are extracted under
their own nodes). Any per-node failure (transport error, API error, or
Lean errors reported in the response) is collected with file context; if
any node failed, the whole extraction fails so the command can exit
non-zero without persisting a partially-extracted manifest.
"""

from __future__ import annotations

import asyncio
import logging
import re
from dataclasses import dataclass
from pathlib import Path

from axle.types import Document

from axle_build_tool.axle_service import AxleService, AxleServiceError
from axle_build_tool.manifest import ExtractedDecl, Manifest, ManifestNode

logger = logging.getLogger(__name__)

_IMPORT_LINE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*(?:--.*)?$")


class ExtractionError(Exception):
    """Raised when at least one node failed extraction.

    The message lists every failing file with its reason; the previous
    manifest should be left untouched by callers.
    """


@dataclass
class FilePayload:
    """A node's isolated payload plus target-attribution bookkeeping."""

    content: str
    #: The payload's lines (same content split into lines).
    lines: list[str]
    #: 1-based first/last line of the target's own section in the payload.
    target_start: int
    target_end: int
    #: Import lines removed from the target's section; used to shift
    #: payload line numbers back to original-file coordinates.
    stripped: int


def _dotted_stem_of(node: ManifestNode) -> str:
    return node.name[len(node.module) + 1:]


def build_file_payload(
    node: ManifestNode,
    manifest: Manifest,
    project_root: Path,
) -> FilePayload:
    """Assemble the standalone extraction payload for one node.

    Dependencies are visited parents-first (the manifest DAG is acyclic
    and already validated), so every declaration appears before its first
    use — Lean files are order-sensitive.

    All `import` lines are removed from the individual file sections
    (intra-project imports are replaced by the inlined content; external
    imports are hoisted into a single deduplicated header block, since
    Lean only allows imports at the beginning of a file).
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

    visit(node)

    hoisted: list[str] = []
    hoisted_seen: set[str] = set()
    sections: list[list[str]] = []
    target_stripped = 0
    for member in order:
        source = (project_root / member.path).read_text(encoding="utf-8")
        internal_stems = {
            _dotted_stem_of(by_name[parent_name]) for parent_name in member.parents
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
            if member.name == node.name:
                target_stripped = stripped
        sections.append(section)

    lines: list[str] = []
    if hoisted:
        lines.extend(hoisted)
        lines.append("")
    payload = FilePayload(
        content="", lines=[], target_start=0, target_end=0, stripped=target_stripped
    )
    for index, section in enumerate(sections):
        if index:
            lines.append("")
        if order[index].name == node.name:
            payload.target_start = len(lines) + 1
        lines.extend(section)
        if order[index].name == node.name:
            payload.target_end = len(lines)
    payload.lines = lines
    payload.content = "\n".join(lines) + "\n"
    return payload


_IMPORT_KEYWORD = re.compile(
    r"^\s*(theorem|lemma|def|abbrev|instance|structure|class|inductive|example)\b"
)


def _decl_from_document(
    doc: Document,
    payload: FilePayload,
) -> ExtractedDecl | None:
    """Map an extracted document to target-file coordinates.

    Axle reports `line_pos` zero-based within the submitted payload;
    convert to one-based payload coordinates, keep only documents that
    belong to the node's own file section (documents of inlined
    dependencies are extracted under their own nodes), and shift back
    into original-file coordinates (every import line stripped from the
    section sat above the declarations, so they shift everything down by
    `stripped`).

    Axle's reported start can land on the declaration's docstring rather
    than on the `theorem`/`def` keyword itself (observed with multi-line
    docstrings); scan forward (bounded) to the keyword line so the stored
    position reliably points at the declaration.
    """
    if not (payload.target_start <= doc.line_pos + 1 <= payload.target_end):
        return None
    offset = payload.stripped - (payload.target_start - 1) + 1
    keyword_line = doc.line_pos + 1
    bound = min(payload.target_end, keyword_line + 64)
    scanned = 0
    while scanned < 64 and keyword_line <= bound and not _IMPORT_KEYWORD.match(
        payload.lines[keyword_line - 1]
    ):
        keyword_line += 1
        scanned += 1
    if scanned > 64 or keyword_line > payload.target_end:
        keyword_line = doc.line_pos + 1  # keep the reported position
    shift = keyword_line - (doc.line_pos + 1)
    return ExtractedDecl(
        name=doc.name,
        kind=doc.kind,
        is_sorry=doc.is_sorry,
        line_pos=doc.line_pos + offset + shift,
        end_line_pos=doc.end_line_pos + offset + shift,
        signature=doc.signature,
    )


async def _extract_node(
    service: AxleService,
    node: ManifestNode,
    manifest: Manifest,
    project_root: Path,
    semaphore: asyncio.Semaphore,
) -> tuple[ManifestNode, str | None]:
    """Extract one node. Returns (updated_node, failure_message_or_None)."""
    try:
        payload = build_file_payload(node, manifest, project_root)
        async with semaphore:
            response = await service.extract_decls(payload.content, context=node.path)
    except AxleServiceError as exc:
        return node, f"{node.path}: {exc}"
    except OSError as exc:
        return node, f"{node.path}: could not read source: {exc}"

    if response.lean_messages.errors:
        return node, (
            f"{node.path}: Axle reported Lean errors: "
            f"{'; '.join(response.lean_messages.errors)}"
        )

    declarations = [
        declaration
        for document in sorted(response.documents.values(), key=lambda d: d.line_pos)
        if (declaration := _decl_from_document(document, payload)) is not None
    ]
    return (
        node.model_copy(update={"extraction": "ok", "declarations": declarations}),
        None,
    )


async def apply_extraction(
    service: AxleService,
    manifest: Manifest,
    project_root: Path,
) -> Manifest:
    """Extract declarations for every node lacking valid extraction data.

    Nodes whose `extraction` is already `"ok"` are skipped (their data was
    carried over by `build_manifest`). Calls are fanned out concurrently,
    bounded by the client's `max_concurrency`. Raises `ExtractionError`
    listing all failures if any node failed; the returned manifest is only
    meant to be persisted when extraction fully succeeds.
    """
    pending = [node for node in manifest.nodes if node.extraction != "ok"]
    if not pending:
        return manifest

    semaphore = asyncio.Semaphore(service.max_concurrency)
    results = await asyncio.gather(
        *(
            _extract_node(service, node, manifest, project_root, semaphore)
            for node in pending
        )
    )

    failures = [message for _, message in results if message is not None]
    if failures:
        raise ExtractionError(
            "\n".join(
                ["Failed to extract declarations:"]
                + [f"  - {failure}" for failure in failures]
            )
        )

    updated = {node.name: node for node, _ in results}
    nodes = [updated.get(node.name, node) for node in manifest.nodes]
    return manifest.model_copy(update={"nodes": nodes})
