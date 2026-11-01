"""Applying Axle declaration extraction to manifest nodes.

Files that use intra-project imports cannot be evaluated standalone by
the Axle API (their project references would not resolve), so
`apply_extraction` submits an *isolated payload* per node (assembled by
`axle_build_tool.payloads`) with the dependencies' declarations
**stubbed to their signatures**: extraction only consumes the node's own
spans and signatures, dependency documents are dropped, and proof
bodies (the most expensive thing to elaborate) never need to reach a
Lean worker during extraction.  The node's own declarations are
extracted from its real, unstubbed source.
The node's transitive
dependencies are nonetheless inlined in topological order (their
signature skeletons supply the referenced symbols), and any per-node
failure (transport error, API error, or Lean errors reported in the
response) is collected with file context; if any node failed, the whole
extraction fails so the command can exit non-zero without persisting a
partially-extracted manifest. Note that with stubbed dependencies the
payload's Lean-errors verdict no longer certifies the dependencies'
proofs — each dependency's own extraction (and later check/verify) does
that.

Declaration-free nodes (import-only aggregates: a docstring plus
imports) skip their extraction request entirely — they'd otherwise pay
a full dependency-closure extraction payload for an empty document set.
Detection is on the whole source text, so it errs toward extraction:
any declaration keyword anywhere (even one mentioned in a docstring)
keeps the normal request. Skipped nodes are recorded with an empty
declaration list, like an extraction that found nothing.
"""

from __future__ import annotations

import asyncio
import logging
import re
import time
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
    # The document's local dependency lists (type / value / syntactic)
    # union into one deduplicated, sorted list — the split itself is
    # tooltip-grade detail, the graph only needs the names. The
    # external variants are kept separately so graph consumers can
    # render them without node explosion. Names come from the
    # payload's content, whose dependency closure is signature-stubbed
    # (extraction stubs dependencies' bodies), so a dependency's
    # reported name is exactly what its own declaration (or stub line)
    # declares — the same bare name an extracting API reports for it.
    dependencies = sorted(
        {
            *doc.local_type_dependencies,
            *doc.local_value_dependencies,
            *doc.local_syntactic_dependencies,
        }
    )
    external_dependencies = sorted(
        {
            *doc.external_type_dependencies,
            *doc.external_value_dependencies,
            *doc.external_syntactic_dependencies,
        }
    )
    return ExtractedDecl(
        name=doc.name,
        kind=doc.kind,
        is_sorry=doc.is_sorry,
        line_pos=line_pos,
        end_line_pos=end_line_pos,
        signature=doc.signature,
        dependencies=dependencies,
        external_dependencies=external_dependencies,
    )


#: Declaration keywords as they can appear anywhere in Lean source. Used
#: only for the conservative declaration-free check: a file is skipped
#: when none of these words occur at all.
_DECLARATION_KEYWORD_SEARCH = re.compile(
    r"\b(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|example)\b"
)


def _source_has_declarations(project_root: Path, node: ManifestNode) -> bool:
    """Whether a node's source text mentions any declaration keyword.

    Reading is forgiving: on an OSError the safest answer is `True`, so
    the normal extraction path runs and surfaces a proper per-node
    failure message.
    """
    try:
        source = (project_root / node.path).read_text(encoding="utf-8")
    except OSError:
        return True
    return _DECLARATION_KEYWORD_SEARCH.search(source) is not None


async def _extract_node(
    service: AxleService,
    node: ManifestNode,
    manifest: Manifest,
    project_root: Path,
    semaphore: asyncio.Semaphore,
) -> tuple[ManifestNode, str | None]:
    """Extract one node. Returns (updated_node, failure_message_or_None)."""
    started: float | None = None
    try:
        payload = build_file_payload(node, manifest, project_root, stub_dependencies=True)
        async with semaphore:
            logger.info(
                "dispatch %s (%d payload lines)",
                node.name,
                len(payload.lines),
            )
            started = time.monotonic()
            response = await service.extract_decls(payload.content, context=node.path)
            logger.info(
                "extracted %s in %.1fs (%d declarations)",
                node.name,
                time.monotonic() - started,
                len(response.documents),
            )
    except AxleServiceError as exc:
        elapsed = time.monotonic() - started if started is not None else -1.0
        logger.info("extraction %s FAILED after %.1fs (%s)", node.name, elapsed, exc)
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

    submitted: list[ManifestNode] = []
    results: list[tuple[ManifestNode, str | None]] = []
    for node in pending:
        if _source_has_declarations(project_root, node):
            submitted.append(node)
        else:
            logger.info(
                "skipping extraction of %s (declaration-free: no declaration "
                "keywords in the source)",
                node.name,
            )
            results.append(
                (
                    node.model_copy(update={"declarations": [], "request_id": None}),
                    None,
                )
            )

    semaphore = asyncio.Semaphore(service.max_concurrency)
    if submitted:
        submitted_results = await asyncio.gather(
            *(
                _extract_node(service, node, manifest, project_root, semaphore)
                for node in submitted
            )
        )
        results = [*results, *submitted_results]

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
