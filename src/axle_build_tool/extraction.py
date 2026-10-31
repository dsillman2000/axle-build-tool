"""Applying Axle declaration extraction to manifest nodes.

Files that use intra-project imports cannot be evaluated standalone by
the Axle API (their project references would not resolve), so
`apply_extraction` submits an *isolated payload* per node (assembled by
`axle_build_tool.payloads`): the node's transitive dependencies inlined
in topological order, followed by the node's own source.

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
from pathlib import Path

from axle.types import Document

from axle_build_tool.axle_service import AxleService, AxleServiceError
from axle_build_tool.manifest import ExtractedDecl, Manifest, ManifestNode
from axle_build_tool.payloads import build_file_payload

logger = logging.getLogger(__name__)

#: Declaration keyword heads, used to snap reported line positions onto the
#: declaration's keyword line.
_DECLARATION_KEYWORD = re.compile(
    r"^\s*(theorem|lemma|def|abbrev|instance|structure|class|inductive|example)\b"
)


class ExtractionError(Exception):
    """Raised when at least one node failed extraction.

    The message lists every failing file with its reason; the previous
    manifest should be left untouched by callers.
    """


def _decl_from_document(
    doc: Document,
    payload: Payload,
    node_name: str,
) -> ExtractedDecl | None:
    """Map an extracted document to target-file coordinates.

    Axle reports `line_pos`/`end_line_pos` one-based and inclusive
    within the submitted payload (verified live: the start may land on
    the declaration's docstring rather than on the `theorem`/`def`
    keyword itself, and the end is the declaration's last line). Keep
    only documents that belong to the node's own file section (documents
    of inlined dependencies are extracted under their own nodes), and
    map back into original-file coordinates exactly via the payload's
    line map (import lines stripped from the section simply have no
    counterpart).

    Because the reported start can sit on a (multi-line) docstring, scan
    forward (bounded) to the keyword line so the stored position
    reliably points at the declaration.
    """
    section_start, section_end = payload.sections[node_name]
    line_map = payload.line_map[node_name]
    start = doc.line_pos
    if not (section_start <= start <= section_end):
        return None
    keyword_line = start
    bound = min(section_end, keyword_line + 64)
    scanned = 0
    while scanned < 64 and keyword_line <= bound and not _DECLARATION_KEYWORD.match(
        payload.lines[keyword_line - 1]
    ):
        keyword_line += 1
        scanned += 1
    if scanned > 64 or keyword_line > section_end:
        keyword_line = start  # keep the reported position
    line_pos = line_map[keyword_line - section_start]
    end = doc.end_line_pos
    if section_start <= end <= section_end:
        end_line_pos = line_map[end - section_start]
    else:
        # Out-of-section ends keep the declaration's own length.
        end_line_pos = line_pos + (end - keyword_line)
    return ExtractedDecl(
        name=doc.name,
        kind=doc.kind,
        is_sorry=doc.is_sorry,
        line_pos=line_pos,
        end_line_pos=end_line_pos,
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
        if (declaration := _decl_from_document(document, payload, node.name)) is not None
    ]
    return (
        node.model_copy(
            update={
                "declarations": declarations,
                "request_id": (response.info or {}).get("request_id"),
            }
        ),
        None,
    )


async def apply_extraction(
    service: AxleService,
    manifest: Manifest,
    project_root: Path,
) -> Manifest:
    """Extract declarations for every node that isn't carried over.

    Nodes with `status == "clean"` already hold valid extraction data
    (carried over by `build_manifest` — compile persists nothing unless
    every node extracted cleanly). Calls are fanned out concurrently,
    bounded by the client's `max_concurrency`. Raises `ExtractionError`
    listing all failures if any node failed; the returned manifest is only
    meant to be persisted when extraction fully succeeds.
    """
    pending = [node for node in manifest.nodes if node.status != "clean"]
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
