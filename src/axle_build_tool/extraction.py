"""Applying Axle declaration extraction to manifest nodes.

Files that use intra-project imports cannot be evaluated standalone by
the Axle API (their project references would not resolve), so
`apply_extraction` submits an *isolated payload* per node (assembled by
`axle_build_tool.payloads`) with the dependencies' declarations
**stubbed to their signatures** and `elaborate_proofs=False`: signatures,
theorem statements, and `def`/`structure`/`class`/`instance` bodies are
elaborated and checked, while theorem proof bodies are replaced with
`sorry` on the server so proof-heavy files extract quickly. Because
`elaborate_proofs=False` omits `is_sorry` and `local_value_dependencies`
on theorems, extraction supplements both locally from the node's source
text (keeping `verify`'s local `sorry` gate, `--select` trimming, and
`axbt graph` proof edges accurate).

The node's transitive dependencies are inlined in topological order
(their signature skeletons supply the referenced symbols), and any
per-node failure (transport error, API error, or Lean errors reported in
the response) is collected with file context; if any node failed, the
whole extraction fails so the command can exit non-zero without
persisting a partially-extracted manifest. Proof-body errors are
deferred to `check` and `verify`.

A failed node's extraction payload is persisted like a failing
submission: the exact content sent (inlined, hoisted, and stubbed as
the extracted quotes) plus the payload→source position map land in
`.axbt/failed/` with the `extract` tier, so the diagnostics' payload
coordinates autopsie offline instead of requiring a hand rebuild of the
composition.

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

import click

from axle.types import Document

from axle_build_tool.axle_service import AxleService, AxleServiceError
from axle_build_tool.manifest import (
    ExtractedDecl,
    Manifest,
    ManifestNode,
    closure_nodes,
)
from axle_build_tool.payloads import (
    Payload,
    build_file_payload,
    persist_failed_payload,
)
from axle_build_tool.report import clock, item_counter, timing_text
from axle_build_tool.stubbing import DECLARATION_HEAD, PROOF_KINDS

logger = logging.getLogger(__name__)


class ExtractionError(Exception):
    """Raised when at least one node failed extraction.

    The message lists every failing file with its reason; the previous
    manifest should be left untouched by callers.
    """


#: Explicit `sorry` / `admit` tokens in comment/string-stripped Lean code.
_SORRY_WORD = re.compile(r"(?<![\w'!?₀-₉«])(?:sorry|admit)(?![\w'!?₀-₉»])")
#: Qualified or bare identifier chains outside leading-dot projections.
_IDENT_CHAIN = re.compile(r"(?<![\w.'])[^\W\d][\w'₀-₉]*(?:\.[^\W\d][\w'₀-₉]*)*")


def _lean_code_only(source: str) -> str:
    """Return `source` with comments, string literals, and char literals blanked.

    Preserves line count (`\\n` boundaries never shift) so declarations stay
    indexable by their 1-based line spans. Strings are consumed across lines
    to avoid false positives inside prose; block comments honor Lean nesting
    and insert a space when closing mid-line so flanked tokens stay separated.
    """
    out: list[str] = []
    i = 0
    n = len(source)
    depth = 0
    in_string = False
    string_escape = False
    just_consumed_char = False

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
                out.append(" ")
            if c == "\n":
                out.append("\n")
            i += 1
            continue

        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if source.startswith("-/", i):
                depth -= 1
                i += 2
                if depth == 0:
                    out.append(" ")
                continue
            if c == "\n":
                out.append("\n")
            i += 1
            continue

        if source.startswith("/-", i):
            depth = 1
            i += 2
            continue

        if source.startswith("--", i):
            i += 2
            while i < n and source[i] != "\n":
                i += 1
            continue

        if c == '"':
            in_string = True
            string_escape = False
            i += 1
            continue

        if c == "'" and not (
            i > 0
            and (source[i - 1].isalnum() or source[i - 1] in "_'")
            and not prev_consumed_char
        ):
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
            if closed:
                out.append(" ")
                just_consumed_char = True
                i = j
                continue

        out.append(c)
        i += 1

    return "".join(out)


def _decl_contains_sorry(
    source_lines: list[str] | None,
    line_pos: int,
    end_line_pos: int,
) -> bool:
    """Whether a declaration's raw span uses `sorry` or `admit`.

    Extraction sends `elaborate_proofs=False`, where the API substitutes
    `sorry` for theorem proofs before elaborating and therefore reports
    `is_sorry=False` on all theorems. Scanning the comment/string-stripped
    declaration span preserves accurate `is_sorry` flags locally.
    """
    if source_lines is None:
        return False
    start = max(0, line_pos - 1)
    end = min(len(source_lines), end_line_pos)
    if start >= end:
        return False
    cleaned = _lean_code_only("\n".join(source_lines[start:end]))
    return _SORRY_WORD.search(cleaned) is not None


def _proof_body_text(cleaned_decl: str) -> str:
    """Return the proof-body suffix of a comment/string-stripped declaration.

    Finds the top-level `:=` (outside `()`, `[]`, `{}`) so default
    binder arguments like `(h : a = 0 := rfl)` aren't mistaken for the
    proof delimiter. Pattern-matching proofs with no top-level `:=` fall
    back to the first top-level `|`, or the text after line 1 if neither
    delimiter appears.
    """
    depth = 0
    first_pipe: int | None = None
    i = 0
    n = len(cleaned_decl)
    while i < n:
        c = cleaned_decl[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0:
            if cleaned_decl.startswith(":=", i):
                return cleaned_decl[i + 2 :]
            if c == "|" and first_pipe is None:
                first_pipe = i
        i += 1
    if first_pipe is not None:
        return cleaned_decl[first_pipe + 1 :]
    # Fallback when signature parsing didn't find `:=` / `|`: skip header line.
    if "\n" in cleaned_decl:
        return cleaned_decl.split("\n", 1)[1]
    return ""


def _supplement_proof_dependencies(
    manifest: Manifest,
    project_root: Path,
    extracted_node_names: set[str],
) -> Manifest:
    """Supplement proof-body dependencies omitted by `elaborate_proofs=False`.

    The API computes full `local_type_dependencies` and full dependencies
    on definitions/structures/instances, but replaces theorem proofs with
    `sorry` before elaboration and leaves theorem `local_value_dependencies`
    empty. Scanning each freshly extracted theorem's proof body for
    identifier references to declarations in its file-closure keeps
    `--select` trimming and `axbt graph` complete across proof edges.
    """
    if not extracted_node_names:
        return manifest

    updated_nodes: list[ManifestNode] = []
    for node in manifest.nodes:
        if node.name not in extracted_node_names or not any(
            d.kind in PROOF_KINDS for d in node.declarations
        ):
            updated_nodes.append(node)
            continue

        try:
            raw = (project_root / node.path).read_text(encoding="utf-8")
        except OSError:
            updated_nodes.append(node)
            continue
        cleaned_lines = _lean_code_only(raw).splitlines()

        # Build lookup from exact or `.`-suffix spelling -> candidate
        # `(owner_node_name, line_pos, decl_name)` in this node's closure.
        closure = closure_nodes(manifest, [node])
        by_suffix: dict[str, list[tuple[str, int, str]]] = {}
        for owner_name, owner in closure.items():
            for cand in owner.declarations:
                entry = (owner_name, cand.line_pos, cand.name)
                parts = cand.name.split(".")
                for start_idx in range(len(parts)):
                    suffix = ".".join(parts[start_idx:])
                    by_suffix.setdefault(suffix, []).append(entry)

        new_decls: list[ExtractedDecl] = []
        changed = False
        for decl in node.declarations:
            if decl.kind not in PROOF_KINDS:
                new_decls.append(decl)
                continue
            start = max(0, decl.line_pos - 1)
            end = min(len(cleaned_lines), decl.end_line_pos)
            if start >= end:
                new_decls.append(decl)
                continue
            proof_text = _proof_body_text("\n".join(cleaned_lines[start:end]))
            extra: set[str] = set()
            for match in _IDENT_CHAIN.finditer(proof_text):
                chain = match.group(0)
                if chain.startswith("_root_."):
                    chain = chain[len("_root_.") :]
                if not chain or chain == "_":
                    continue
                segments = chain.split(".")
                # Test every prefix `p_0`, `p_0.p_1`, ... so projection
                # syntax like `up_thm.symm` still resolves to `Foo.up_thm`.
                for prefix_len in range(1, len(segments) + 1):
                    prefix = ".".join(segments[:prefix_len])
                    for owner_name, cand_line, cand_name in by_suffix.get(prefix, ()):
                        if cand_name == decl.name:
                            continue
                        if owner_name == node.name and cand_line >= decl.line_pos:
                            continue
                        extra.add(cand_name)
            if extra:
                merged = sorted(set(decl.dependencies) | extra)
                if merged != decl.dependencies:
                    decl = decl.model_copy(update={"dependencies": merged})
                    changed = True
            new_decls.append(decl)

        updated_nodes.append(
            node.model_copy(update={"declarations": new_decls}) if changed else node
        )

    return manifest.model_copy(update={"nodes": updated_nodes})


def _decl_from_document(
    doc: Document,
    payload: Payload,
    node_name: str,
    source_lines: list[str] | None = None,
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
    forward (bounded) to the keyword line — the declaration's header
    may carry modifiers (`private`, `protected`, …) — so the stored
    position reliably points at the declaration.
    """
    section_start, section_end = payload.sections[node_name]
    line_map = payload.line_map[node_name]
    start = doc.line_pos
    if not (section_start <= start <= section_end):
        return None
    bound = min(section_end, doc.end_line_pos, start + 64)
    keyword_line = start
    comment_depth = 0
    found = False
    while keyword_line <= bound:
        line = payload.lines[keyword_line - 1]
        i = 0
        n = len(line)
        while i < n:
            if comment_depth > 0:
                if line.startswith("/-", i):
                    comment_depth += 1
                    i += 2
                elif line.startswith("-/", i):
                    comment_depth -= 1
                    i += 2
                else:
                    i += 1
            else:
                while i < n and line[i].isspace():
                    i += 1
                if line.startswith("/-", i):
                    comment_depth = 1
                    i += 2
                else:
                    break
        if comment_depth == 0:
            match = DECLARATION_HEAD.match(line[i:])
            if match is not None and match.group("kind") == doc.kind:
                found = True
                break
        keyword_line += 1
    if not found:
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
        is_sorry=doc.is_sorry or _decl_contains_sorry(source_lines, line_pos, end_line_pos),
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


def _persist_and_report(
    payload: Payload,
    node: ManifestNode,
    manifest: Manifest,
    project_root: Path,
    request_id: str | None,
    failure: str,
) -> str:
    """Persist a failed extraction payload; return the failure message.

    The extraction payload is the shape the reported coordinates refer
    to (dependencies inlined and stubbed, imports hoisted, minification
    never applied here), so it lands in `.axbt/failed/` beside the
    check/verify failures, keyed on the extraction's request id when
    the API assigned one. Persistence is best-effort: an I/O failure
    keeps the plain failure message.
    """
    paths = {member.name: member.path for member in manifest.nodes}
    try:
        lean_path, map_path = persist_failed_payload(
            payload.content,
            payload,
            project_root=project_root,
            request_id=request_id,
            tier="extract",
            paths=paths,
        )
    except OSError:
        return failure
    shown = lambda path: str(path.relative_to(project_root).as_posix())
    return f"{failure} (payload saved: {shown(lean_path)} + {shown(map_path)})"


async def _extract_node(
    service: AxleService,
    node: ManifestNode,
    manifest: Manifest,
    project_root: Path,
    semaphore: asyncio.Semaphore,
    *,
    label_width: int,
    counter_position: int,
    counter_total: int,
) -> tuple[ManifestNode, str | None]:
    """Extract one node, streaming its report line pair.

    Prints the dbt-style START when its dispatch acquires the
    semaphore, and the verdict (OK with the measured duration, or FAIL
    with the reason) the moment its response completes — completion
    order, so a slow node's wall time is visible while the run lives
    rather than only in the summary. Returns (updated_node,
    failure_message_or_None).
    """
    payload: Payload | None = None
    started: float | None = None
    source_lines: list[str] | None = None
    counter = f"{item_counter(counter_position, counter_total)} "
    try:
        payload = build_file_payload(node, manifest, project_root, stub_dependencies=True)
        source_lines = (project_root / node.path).read_text(encoding="utf-8").splitlines()
        async with semaphore:
            click.echo(
                f"{clock()} {counter}{node.name:<{label_width}}  "
                f"{click.style('START', fg='white')}  [RUN]"
            )
            started = time.monotonic()
            response = await service.extract_decls(
                payload.content,
                context=node.path,
                elaborate_proofs=False,
            )
            elapsed = time.monotonic() - started
            logger.info(
                "extracted %s in %.1fs (%d declarations)",
                node.name,
                elapsed,
                len(response.documents),
            )
            failed = bool(response.lean_messages.errors)
            click.echo(
                f"{clock()} {counter}{node.name:<{label_width}}  "
                f"{click.style('FAIL' if failed else 'OK', fg='red' if failed else 'green')}  "
                f"{timing_text(elapsed)}"
            )
            if failed:
                failure = (
                    f"{node.path}: Axle reported Lean errors: "
                    f"{'; '.join(response.lean_messages.errors)}"
                )
                rid = (response.info or {}).get("request_id")
                failure = _persist_and_report(
                    payload, node, manifest, project_root, rid, failure
                )
                click.echo(f"    {failure}")
                return node, failure
    except AxleServiceError as exc:
        elapsed = time.monotonic() - started if started is not None else -1.0
        logger.info("extraction %s FAILED after %.1fs (%s)", node.name, elapsed, exc)
        if started is not None:
            elapsed_text = timing_text(elapsed)
        else:
            elapsed_text = ""
        failure = f"{node.path}: {exc}"
        if payload is not None:
            # The transport failure arrived with the payload built (or
            # mid-submission), so the exact content sent autopsies too;
            # there is no response, so the id-keyed name falls back to
            # the timestamp stem.
            failure = _persist_and_report(
                payload, node, manifest, project_root, None, failure
            )
        if started is not None:
            click.echo(
                f"{clock()} {counter}{node.name:<{label_width}}  "
                f"{click.style('FAIL', fg='red')}  {elapsed_text}"
            )
            click.echo(f"    {failure}")
        return node, failure
    except OSError as exc:
        return node, f"{node.path}: could not read source: {exc}"

    declarations = [
        declaration
        for document in sorted(response.documents.values(), key=lambda d: d.line_pos)
        if (
            declaration := _decl_from_document(
                document, payload, node.name, source_lines=source_lines
            )
        )
        is not None
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

    The streaming report prints one pair per submitted node — dbt-style
    START at dispatch and a verdict (OK with the measured duration, or
    FAIL with the reason) at completion — so a slow extraction's wall
    time is visible while the run lives. Declaration-free skip nodes
    print a dim SKIP line (no API call, no duration). The counter's
    denominator is the pending-node count; carried-over files are not
    extraction tasks.
    """
    pending = [node for node in manifest.nodes if node.status != "clean"]
    if not pending:
        return manifest

    counter_total = len(pending)
    headline = {node.name: position for position, node in enumerate(pending, start=1)}
    label_width = max(len(node.name) for node in pending)
    submitted: list[ManifestNode] = []
    results: list[tuple[ManifestNode, str | None]] = []
    for pending_position, node in enumerate(pending, start=1):
        if _source_has_declarations(project_root, node):
            submitted.append(node)
            continue
        logger.info(
            "skipping extraction of %s (declaration-free: no declaration "
            "keywords in the source)",
            node.name,
        )
        click.echo(
            f"{clock()} {item_counter(pending_position, counter_total)} "
            f"{node.name:<{label_width}}  "
            f"{click.style('SKIP', dim=True)}"
        )
        click.secho(
            "    no extraction needed: declaration-free (imports/comments only)",
            dim=True,
        )
        results.append(
            (
                node.model_copy(update={"declarations": [], "request_id": None}),
                None,
            )
        )

    semaphore = asyncio.Semaphore(service.max_concurrency)
    if submitted:
        # Gate each pending node on its pending parents so downstream
        # payloads see freshly extracted upstream declarations and
        # `stub_dependencies=True` actually stubs upstream proof bodies
        # on initial compile, upstream edits, and `--full-refresh` (#51).
        live_nodes: dict[str, ManifestNode] = {
            node.name: node for node in manifest.nodes
        }
        for skipped_node, _ in results:
            live_nodes[skipped_node.name] = skipped_node
        done_events: dict[str, asyncio.Event] = {
            node.name: asyncio.Event() for node in submitted
        }

        async def _run_node(node: ManifestNode) -> tuple[ManifestNode, str | None]:
            for parent_name in node.parents:
                parent_event = done_events.get(parent_name)
                if parent_event is not None:
                    await parent_event.wait()
            try:
                current_manifest = manifest.model_copy(
                    update={"nodes": [live_nodes[n.name] for n in manifest.nodes]}
                )
                updated_node, failure = await _extract_node(
                    service,
                    node,
                    current_manifest,
                    project_root,
                    semaphore,
                    label_width=label_width,
                    counter_position=headline[node.name],
                    counter_total=counter_total,
                )
                if failure is None:
                    live_nodes[node.name] = updated_node
                return updated_node, failure
            finally:
                done_events[node.name].set()

        submitted_results = await asyncio.gather(
            *(_run_node(node) for node in submitted)
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
    updated_manifest = manifest.model_copy(update={"nodes": nodes})
    return _supplement_proof_dependencies(
        updated_manifest,
        project_root,
        {node.name for node in submitted},
    )
