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

import json
import re
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence

from axle_build_tool.config import CACHE_DIRNAME
from axle_build_tool.manifest import Manifest, ManifestNode, reachable_declarations
from axle_build_tool.minify import Minified, minify_lines
from axle_build_tool import stubbing
from axle_build_tool.stubbing import PROOF_KINDS, stubbed_source

_IMPORT_LINE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*(?:--.*)?$")

#: A line opening a scoped-option prefix (`set_option … in`) that Lean
#: attaches to the next command — i.e. to the declaration its span covers.
#: Only the split-line form matters here: `set_option … in theorem …` on a
#: single line is inside the declaration's own span. Responsible for the
#: dangling `in`-continuations of issue 41 (the payload parser receiving
#: the trimmed content sees `set_option` as a standalone command).
_SCOPED_OPTION_PREFIX_LINE = re.compile(r"^\s*set_option\s+.+\bin\s*$")

#: Subdirectory of the cache holding persisted payloads.
COMPILED_DIRNAME = "compiled"

#: Subdirectory of the cache holding failed submissions' payloads and
#: position maps (`.axbt/failed/`). Sibling of `compiled/` so the
#: compiled-payload GC pass never has to special-case it.
FAILED_DIRNAME = "failed"


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
    #: Node name -> set of declaration names actually retained in that
    #: node's section after trimming (empty => every extracted
    #: declaration is present, i.e. no trimming happened).
    kept: dict[str, set[str]] = field(default_factory=dict)


def dotted_stem_of(node: ManifestNode) -> str:
    """The dotted file stem of a node: `Utils/Basic.lean` -> `Utils.Basic`."""
    return node.name[len(node.module) + 1:]


_NOT_STUBBED = object()


def _is_stubbed_decl(declaration, stubbed_only) -> bool:
    """Whether `declaration` is stubbed under the `--sorry` settings."""
    if stubbed_only is _NOT_STUBBED:
        return False
    if declaration.kind not in PROOF_KINDS:
        return False
    if stubbed_only is None:
        return True
    return declaration.name in stubbed_only


def _transform_member_source(
    node: ManifestNode,
    source: str,
    stubbed_only,
    keep_names: set[str] | None,
    warnings: list[str] | None = None,
) -> tuple[str, list[int | None]]:
    """Apply `--sorry` stubbing and declaration trimming to one file.

    Returns the transformed source text and a parallel list mapping each
    surviving transformed line to its original source line number (`None`
    for stub lines, which have no raw-source counterpart). Both
    transformations key on the manifest's raw-file spans, so they can run
    together without one invalidating the other's coordinates.

    The walk is a strict partition of the file's lines: every source line
    is emitted at most once, and the cursor only ever advances past
    content already emitted. Spans are also clamped to the next
    declaration's line — two declarations cannot share a line, so a span
    reaching past its neighbor is corrupt (mis-snapped or overshooting).
    Declarations whose spans fail these checks keep their real source and
    lose only their stub/trim treatment, keeping the payload's content
    complete even when a manifest is stale.

    Trimmed declarations leave with what Lean attaches to them: the
    declaration's docstring and any chained `set_option … in` prefixes
    directly above it, plus the blank lines woven between (see the
    trim-extension walk below). Keeping those behind detaches scoped
    options from their declaration — a payload ending in a stranded
    `set_option … in` fails to parse outright.
    """
    lines = source.splitlines()
    if not lines:
        return source, []

    node_decl_names = {d.name for d in node.declarations}
    if keep_names is not None and not (node_decl_names & keep_names):
        # Conservative: no recorded dependency reaches this file, so
        # keep it whole rather than risk dropping elaboration context.
        keep_names = None

    # Fast path: nothing to do.
    if stubbed_only is _NOT_STUBBED and (keep_names is None or all(
        d.name in keep_names for d in node.declarations
    )):
        return source, list(range(1, len(lines) + 1))

    ordered = sorted(node.declarations, key=lambda d: d.line_pos)
    #: Exclusive line bound per declaration, clamped to the next
    #: declaration's first line (sibling spans never overlap lines).
    capped = []
    for position, declaration in enumerate(ordered):
        cap = (
            ordered[position + 1].line_pos - 1
            if position + 1 < len(ordered)
            else len(lines)
        )
        capped.append(min(declaration.end_line_pos, cap))

    out_lines: list[str] = []
    out_orig: list[int | None] = []
    cursor = 0
    for index, declaration in enumerate(ordered):
        start = declaration.line_pos - 1
        end = capped[index]
        # Defensive: stale/overlapping spans are left untouched. The raw
        # end matters here: an end past the file's last line is corrupt.
        stale = (
            start < cursor
            or start >= end
            or declaration.end_line_pos > len(lines)
            or not stubbing._span_head_matches(lines[start], declaration.kind)
        )
        kept = keep_names is None or declaration.name in keep_names

        # For trimmed declarations, extend the removed span upward so the
        # lines Lean attaches to the declaration go with it: its
        # directly-preceding docstring, and any directly-preceding chained
        # `set_option … in` scoped-option prefixes (in either order, with
        # blank lines woven between). Dropping the declaration without
        # them strands the prefix above whatever survives — or as the
        # payload section's last content, where the API parser sees
        # `set_option … in` as an unterminated command (issue 41).
        trim_start = start
        if (not kept) and (not stale):
            probe = start - 1
            while probe >= cursor:
                if lines[probe].strip() == "":
                    probe -= 1
                    continue
                if _SCOPED_OPTION_PREFIX_LINE.match(lines[probe]):
                    probe -= 1
                    continue
                if lines[probe].strip().endswith("-/"):
                    open_index = probe
                    while (
                        open_index >= cursor
                        and not lines[open_index].strip().startswith("/-")
                    ):
                        open_index -= 1
                    if open_index < cursor:
                        break
                    probe = open_index - 1
                    continue
                break
            trim_start = probe + 1

        # Lines before the (possibly extended) span survive — and the
        # cursor must never fall behind content already emitted.
        for i in range(cursor, min(trim_start, len(lines))):
            out_lines.append(lines[i])
            out_orig.append(i + 1)
        cursor = max(cursor, min(trim_start, len(lines)))

        if stale:
            if warnings is not None:
                warnings.append(
                    f"{node.path}: declaration '{declaration.name}' could not be "
                    "stubbed (the manifest is out of date with the source); "
                    "run `axbt compile` to rebuild it."
                )
            for i in range(max(start, cursor), min(end, len(lines))):
                out_lines.append(lines[i])
                out_orig.append(i + 1)
            cursor = max(cursor, min(end, len(lines)))
            continue
        if not kept:
            cursor = max(cursor, end)
            continue
        if _is_stubbed_decl(declaration, stubbed_only):
            out_lines.append(stubbing._stub_line(declaration))
            out_orig.append(None)
            cursor = max(cursor, end)
            continue
        for i in range(start, end):
            out_lines.append(lines[i])
            out_orig.append(i + 1)
        cursor = max(cursor, end)

    for i in range(cursor, len(lines)):
        out_lines.append(lines[i])
        out_orig.append(i + 1)

    transformed = "\n".join(out_lines)
    if out_lines and source.endswith("\n"):
        transformed += "\n"
    return transformed, out_orig


def build_payload(
    nodes: Sequence[ManifestNode],
    manifest: Manifest,
    project_root: Path,
    stubbed: dict[str, frozenset[str] | None] | None = None,
    warnings: list[str] | None = None,
    minify: bool = False,
    **kwargs: Any,
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

    `minify` runs the best-effort comment/blank-line stripper per file
    (after stubbing, since manifest spans are keyed to raw source); the
    line maps are built from the surviving lines' original numbers, so
    attribution stays exact on the smaller text. Files that don't track
    cleanly are submitted unminified.
    """
    #: Optional declaration-level trimming: any of these keyword
    #: arguments names the roots (selected declarations) whose transitive
    #: dependency closure should be retained; everything else is dropped.
    _ROOT_KEYS = (
        "selected_declarations",
        "selected",
        "roots",
        "trim_roots",
        "selected_decls",
        "trim_to",
        "keep_declarations",
        "kept_declarations",
        "declarations",
        "keep",
        "trimmed",
    )
    keep_names: set[str] | None = None
    for _key in _ROOT_KEYS:
        if _key in kwargs and kwargs[_key] is not None:
            keep_names = reachable_declarations(manifest, kwargs[_key])
            break

    selected_node_names = {node.name for node in nodes}

    by_name = manifest.by_name()
    order: list[ManifestNode] = []
    seen: set[str] = set()

    # Iterative, cycle-safe, dependencies-first traversal of the file
    # dependency closure. In acyclic graphs, a node is appended to `order`
    # only after all of its resolved parents have been appended.
    for node in sorted(nodes, key=lambda n: n.name):
        stack: list[tuple[ManifestNode, bool]] = [(node, False)]
        while stack:
            current, done = stack.pop()
            if done:
                order.append(current)
                continue
            if current.name in seen:
                continue
            seen.add(current.name)
            stack.append((current, True))
            for parent_name in sorted(current.parents, reverse=True):
                parent = by_name.get(parent_name)
                if parent is not None and parent.name not in seen:
                    stack.append((parent, False))

    hoisted: list[str] = []
    hoisted_seen: set[str] = set()
    sections: list[tuple[ManifestNode, list[str], list[int]]] = []
    kept_map: dict[str, set[str]] = {}
    for member in order:
        raw_source = (project_root / member.path).read_text(encoding="utf-8")
        if stubbed and member.name in stubbed:
            stubbed_only = stubbed[member.name]
        else:
            stubbed_only = _NOT_STUBBED
        member_keep = keep_names
        if member_keep is None:
            kept_for_member = {d.name for d in member.declarations}
        else:
            kept_for_member = set(member_keep) & {d.name for d in member.declarations}
            if not kept_for_member:
                kept_for_member = {d.name for d in member.declarations}
        kept_map[member.name] = kept_for_member
        if stubbed_only is not _NOT_STUBBED or member_keep is not None:
            source, orig_lines = _transform_member_source(
                member, raw_source, stubbed_only, member_keep, warnings=warnings
            )
        else:
            source = raw_source
            orig_lines = None
        tagged: list[tuple[int, str]]
        if minify and (stripped := minify_lines(source)) is not None:
            tagged = []
            for _pos, _text in zip(stripped.source_lines, stripped.lines):
                if orig_lines is not None and 1 <= _pos <= len(orig_lines):
                    _orig = orig_lines[_pos - 1]
                else:
                    _orig = _pos
                if _orig is None:
                    _orig = _pos
                tagged.append((_orig, _text))
        else:
            if orig_lines is not None:
                tagged = []
                for _i, _line in enumerate(source.splitlines(), start=1):
                    _orig = orig_lines[_i - 1] if _i - 1 < len(orig_lines) else _i
                    if _orig is None:
                        _orig = _i
                    tagged.append((_orig, _line))
            else:
                tagged = list(enumerate(source.splitlines(), start=1))
        internal_stems = {
            dotted_stem_of(by_name[parent_name])
            for parent_name in member.parents
            if parent_name in by_name
        }
        section: list[str] = []
        line_numbers: list[int] = []
        for number, line in tagged:
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
    result = Payload(content="", lines=[], sections={}, line_map={}, kept={})
    for index, (member, section, line_numbers) in enumerate(sections):
        if index:
            lines.append("")
        start = len(lines) + 1
        lines.extend(section)
        result.sections[member.name] = (start, len(lines))
        result.line_map[member.name] = line_numbers
    result.lines = lines
    result.content = "\n".join(lines) + "\n"
    result.kept = kept_map
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


def gc_compiled_payloads(manifest: Manifest, project_root: Path) -> list[Path]:
    """Delete stale files under `.axbt/compiled/` ("cache dir ⊋ manifest ⇒ delete").

    A name corresponds to a live manifest state if it is a node's
    `isolated` payload, a persisted `stubbed` variant of that node, or a
    module-level `stubbed`/`isolated` per-selection payload of a module
    that still has nodes. Anything else under the directory (left over
    from a deleted source file, a renamed stem, or a dropped module)
    is removed, since stale module-slug files invite tooling to trust
    code the project no longer contains.

    Runs at manifest-rewrite time — the compile precursor's pass after
    the fresh manifest is known. Files under other cache subdirectories
    (notably `.axbt/failed/`) are untouched; the pass only sweeps
    `compiled/`.
    """
    directory = compiled_payload_dir(project_root)
    if not directory.is_dir():
        return []
    live: set[str] = set()
    for node in manifest.nodes:
        base = f"{node.module}_{dotted_stem_of(node).replace('.', '_')}"
        live.add(f"{base}_isolated.lean")
        live.add(f"{base}_stubbed.lean")
    for module in {node.module for node in manifest.nodes}:
        live.add(f"{module}_isolated.lean")
        live.add(f"{module}_stubbed.lean")
    removed: list[Path] = []
    for entry in sorted(directory.iterdir()):
        if entry.is_file() and entry.name not in live:
            try:
                entry.unlink()
            except OSError:
                continue  # a busy file is re-swept at the next compile
            removed.append(entry)
    return removed


def failed_payload_dir(project_root: Path) -> Path:
    """The `.axbt/failed/` directory of `project_root`."""
    return project_root / CACHE_DIRNAME / FAILED_DIRNAME


def persist_failed_payload(
    content: str,
    payload: Payload,
    *,
    project_root: Path,
    request_id: str | None,
    tier: str,
    paths: dict[str, str],
) -> tuple[Path, Path]:
    """Persist a failing submission's exact payload and position map.

    Writes `<id>.lean` — the submitted content verbatim, the shape the
    FAIL diagnostics' coordinates refer to — and `<id>.map.json` along-
    side it: the payload→source position map (sections, the per-section
    source line lists, and node→source paths) plus the run context.
    Only called on a FAIL verdict; ids key on the API's request id when
    present (opaque stem, falling back to a UTC timestamp), so repeated
    failures of the same selection land side by side instead of
    clobbering each other.
    """
    if request_id:
        stem = re.sub(r"[^A-Za-z0-9._-]", "_", request_id)
    else:
        stem = datetime.now(timezone.utc).strftime("noid-%Y%m%dT%H%M%S.%fZ")
    directory = failed_payload_dir(project_root)
    directory.mkdir(parents=True, exist_ok=True)
    lean_path = directory / f"{stem}.lean"
    map_path = directory / f"{stem}.map.json"
    lean_path.write_text(content, encoding="utf-8")
    map_path.write_text(
        json.dumps(
            {
                "request_id": request_id,
                "tier": tier,
                "sections": {
                    name: list(span) for name, span in payload.sections.items()
                },
                "line_map": payload.line_map,
                "paths": paths,
            },
            indent=1,
        )
        + "\n",
        encoding="utf-8",
    )
    return lean_path, map_path


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


def write_compiled_payloads(
    manifest: Manifest, project_root: Path, minify: bool = False
) -> list[Path]:
    """Persist per-file isolated payloads under `.axbt/compiled/`.

    Returns the written paths, in manifest (name-sorted) order.
    """
    out_dir = compiled_payload_dir(project_root)
    out_dir.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    for node in manifest.nodes:
        payload = build_payload([node], manifest, project_root, minify=minify)
        path = out_dir / compiled_filename(node.module, dotted_stem_of(node))
        path.write_text(payload.content, encoding="utf-8")
        written.append(path)
    return written
