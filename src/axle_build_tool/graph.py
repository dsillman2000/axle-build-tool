"""Offline HTML rendering of the manifest as a Cytoscape.js graph.

`axbt graph` writes a single-page HTML visualization of the manifest's
dependency structure (by default `.axbt/graph.html`): compound nodes
module -> file -> declaration, with file-level import edges and
declaration-to-declaration edges from the extraction dependency lists
(populated by the outcome-record work).

**Colors key only on the outcome stamps, never inferred** (the stamp
contract records only successful, full, unstubbed submissions):

- `verified` (green) — has a verification stamp.
- `checked` (yellow) — has a check stamp but no verification stamp:
  checked-clean in full context, still awaiting kernel verification.
  Declaration kinds that can never verify (defs, ...) land on `done`
  (green), which is their terminal state ("done on their own tier").
- `unchecked` (orange) — neither stamp: never judged by a full,
  unstubbed payload.

Container nodes (files, modules) roll up to the weakest constituent
declaration state (orange > yellow > green); containers with no
extracted declarations (declaration-free import-only files) are
`empty` (grey). Manifests written before the stamp work degrade
automatically to the verified-vs-orange palette — no stub-and-hope
inference anywhere.

The page is interactive (pan/zoom, hover tooltips, click-to-highlight
a node's transitive dependency cone and inspect its metadata, live
search, and edge toggles) from the single pinned Cytoscape.js CDN
script alone. Data reaches the page as JSON embedded in a
`<script type="application/json">` block: `json.dumps` with every
`<`/`>` escaped to `\\u003c`/`\\u003e` — valid JSON that cannot form
`</script>` (or any tag) in the page — and every manifest-derived
string is escaped into tooltip markup with `html.escape`. Names are
never interpolated into HTML raw.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable
import html
import json
from pathlib import Path
from typing import Any

from axle_build_tool.config import CACHE_DIRNAME
from axle_build_tool.manifest import Manifest, ManifestNode, closure_nodes
from axle_build_tool.payloads import dotted_stem_of
from axle_build_tool.stubbing import PROOF_KINDS as _VERIFIABLE_KINDS
from axle_build_tool.stubbing import bare_name

#: Generated graph artifacts live in the cache alongside the payloads.
GRAPH_FILENAME = "graph.html"

#: The page's single external script from a CDN (pinned version; SRI
#: hash computed from the served bytes) — never bundled into axbt,
#: never fetched by it. All layout coordinates are computed
#: deterministically at build time in Python.
CYTOSCAPE_URL = "https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.31.0/cytoscape.min.js"
CYTOSCAPE_INTEGRITY = (
    "sha512-SRHUEtWi7EdmapdotitmlD7tNoeRXCtll4Y0yl2YYJB+m+IuIEvvHjZ7V34/k5ZFBtMN/"
    "uehjaerdJGr7hgt1g=="
)

#: weakest -> strongest; containers roll up to the weakest constituent.
#: `done` ranks after `verified`: it is a never-verifiable kind's
#: terminal state (green), and a container with any kernel-pending
#: member still reads yellow.
_STATES = ["unchecked", "checked", "verified", "done"]
_EMPTY_STATE = "empty"

_LEGEND_TEXT = {
    "verified": "verified — has a kernel verification stamp",
    "checked": "checked — passed typecheck, awaiting kernel verification",
    "done": "done — checked clean, and this kind is never verifiable",
    "unchecked": "unchecked — never judged by a full, unstubbed check",
    _EMPTY_STATE: "empty — a file/module with no declarations extracted",
}

#: The red-asterisk marker for files whose source is new or changed.
_STAR = "\u2731"


def graph_path(project_root: Path) -> Path:
    """The default graph output path: `.axbt/graph.html`."""
    return project_root / CACHE_DIRNAME / GRAPH_FILENAME


def state_of(declaration: Any) -> str:
    """A declaration's pipeline state, keyed strictly on its stamps.

    Never-verifiable kinds (defs, instances, structures, ...) have no
    kernel tier: a clean check is their terminal state, recorded as
    `done` (green) rather than `checked` (yellow — reserved for
    declarations still awaiting kernel verification). Colors key only
    on the stamps, never inferred.
    """
    if declaration.verified_sig or declaration.verified_at:
        return "verified"
    if declaration.checked_sig or declaration.checked_at:
        return "checked" if declaration.kind in _VERIFIABLE_KINDS else "done"
    return "unchecked"


def rollup_state(states: list[str]) -> str:
    """The container state: the weakest constituent declaration's state.

    A declaration-free container is `empty` (grey): nothing was judged
    and nothing can be — not the same fact as "unchecked".
    """
    if not states:
        return _EMPTY_STATE
    return min(states, key=_STATES.index)


def rendered_nodes(
    manifest: Manifest, selected: list[ManifestNode]
) -> list[ManifestNode]:
    """The graph's file set: `selected` plus their full transitive
    dependency closure (the payload-closure walk, dependencies-first).

    `--select` reuses the selection machinery, so the rendered set of a
    declaration selection is its owning file (with all of its
    declarations) and every ancestor; a module selection is every file
    of the module and the union's ancestors.
    """
    rendered = closure_nodes(manifest, selected)
    return [rendered[name] for name in sorted(rendered)]


def _tooltip(title: str, lines: list[tuple[str, str]]) -> str:
    """A pre-escaped tooltip block for the page's JavaScript overlay.

    The title and every value pass through `html.escape` here, so the
    page can hand the result to `innerHTML` without any
    manifest-derived string ever touching HTML raw.
    """
    rows = "".join(
        f'<div class="row"><span class="k">{html.escape(key)}</span>'
        f"<code>{html.escape(value)}</code></div>"
        for key, value in lines
    )
    return f'<div class="tt">{html.escape(title)}</div><div class="rows">{rows}</div>'


#: Re-derive the declaration name from its node id (`decl:<file>:<name>`;
#: file stems and Lean names contain no colons).
def _decl_id_name(decl_id: str) -> str:
    return decl_id.removeprefix("decl:").rsplit(":", 1)[-1]


def _decl_counts_row(declarations: list[Any]) -> str:
    """The `3 verified, 2 checked, 1 unchecked` count line."""
    counts = {state: 0 for state in _STATES}
    for declaration in declarations:
        counts[state_of(declaration)] += 1
    return (
        f"{counts['verified']} verified, {counts['done']} done, "
        f"{counts['checked']} checked (unverified), "
        f"{counts['unchecked']} unchecked"
    )


def _status_text(node: ManifestNode) -> str:
    """The file's diff status with its marker if changed."""
    return f"{node.status} {_STAR}" if node.status in ("new", "changed") else node.status


#: Pill/badge and layered layout geometry constants (pixels).
_PILL_H = 28
_PILL_CHAR_W = 8
_PILL_PAD_X = 34
_PILL_MIN_W = 84

_DECL_ROW_STEP = 36      # 28px node height + 8px vertical gap
_SUBCOL_GAP = 18         # horizontal gap between sub-columns inside one file
_FILE_PAD_X = 20         # horizontal padding around declaration nodes in a file box
_FILE_PAD_Y = 20         # vertical padding around declaration nodes in a file box
_FILE_TITLE_H = 26       # vertical clearance above a file box for its title
_FILE_GAP_Y = 42         # vertical gap between stacked file boxes in a rank column
_RANK_GAP_X = 64         # horizontal gap between file rank columns within a module
_MODULE_PAD_X = 26       # horizontal padding inside a module box
_MODULE_GAP_X = 96       # horizontal gap between adjacent module boxes
_LAYOUT_TOP = 56
_MAX_MODULE_COLS = 4     # cap horizontal rank columns per module for balanced aspect ratio


def _pill_width(label: str) -> int:
    """Pixel width of a declaration pill/badge sized to enclose `label`."""
    return max(_PILL_MIN_W, len(label) * _PILL_CHAR_W + _PILL_PAD_X)


def _subcolumn_count(decl_count: int) -> int:
    """Number of side-by-side declaration sub-columns inside one file card."""
    if decl_count <= 10:
        return 1
    if decl_count <= 24:
        return 2
    if decl_count <= 45:
        return 3
    return 4


def _longest_paths(
    keys: Iterable[str],
    parents_of: Callable[[str], list[str]],
) -> dict[str, int]:
    """Compute longest-path depths iteratively, dropping cycle back-edges."""
    memo: dict[str, int] = {}
    visiting: set[str] = set()
    work: list[tuple[str, list[str] | None]] = []
    for start in keys:
        if start in memo:
            continue
        work.append((start, None))
        while work:
            node, parents = work.pop()
            if parents is not None:
                best = max((memo[p] for p in parents if p in memo), default=-1)
                memo[node] = 1 + best
                visiting.discard(node)
                continue
            if node in memo or node in visiting:
                continue
            visiting.add(node)
            node_parents = parents_of(node)
            work.append((node, node_parents))
            for parent in node_parents:
                if parent not in memo and parent not in visiting:
                    work.append((parent, None))
    return memo


def _order_file_declarations(declarations: list[Any]) -> list[Any]:
    """Order a file's declarations by intra-file dependency depth, then
    source line (`line_pos`), then name."""
    if not declarations:
        return []
    exact = {d.name: d.name for d in declarations}
    by_suffix: dict[str, list[str]] = {}
    for d in declarations:
        by_suffix.setdefault(d.name.rsplit(".", 1)[-1], []).append(d.name)

    intra_parents: dict[str, list[str]] = {}
    for d in declarations:
        parents: set[str] = set()
        for dep in d.dependencies:
            target = exact.get(dep)
            if target is None:
                candidates = by_suffix.get(dep.rsplit(".", 1)[-1], [])
                if len(candidates) == 1:
                    target = candidates[0]
            if target is not None and target != d.name:
                parents.add(target)
        intra_parents[d.name] = sorted(parents)

    ordered_keys = [
        d.name for d in sorted(declarations, key=lambda item: (item.line_pos, item.name))
    ]
    depths = _longest_paths(ordered_keys, lambda name: intra_parents[name])
    return sorted(
        declarations,
        key=lambda d: (depths.get(d.name, 0), d.line_pos, d.name),
    )


def _partition_module_columns(
    members: list[ManifestNode],
    intra_levels: dict[str, int],
    global_levels: dict[str, int],
) -> list[list[ManifestNode]]:
    """Arrange a module's files into left-to-right rank columns.

    When a module has up to `_MAX_MODULE_COLS` distinct intra-module
    dependency levels and each level has at most `_MAX_MODULE_COLS`
    files, every level gets its own dedicated rank column so intra-module
    chains and diamonds lay out directly left-to-right by rank. Larger
    modules wrap their level-ordered topological sequence into up to
    `_MAX_MODULE_COLS` balanced columns so wide or deep modules stay
    compact 2D grids while preserving topological order (every
    intra-module dependency lies strictly in an earlier column to the
    left or higher up in the same column).
    """
    if not members:
        return []
    ordered = sorted(
        members,
        key=lambda n: (intra_levels[n.name], global_levels[n.name], n.name),
    )
    by_rank: dict[int, list[ManifestNode]] = {}
    for node in ordered:
        by_rank.setdefault(intra_levels[node.name], []).append(node)
    ranks = [by_rank[r] for r in sorted(by_rank)]
    if len(ranks) <= _MAX_MODULE_COLS and all(
        len(group) <= _MAX_MODULE_COLS for group in ranks
    ):
        return ranks

    num_cols = min(_MAX_MODULE_COLS, max(2, len(ranks)))
    if len(ranks) == 1:
        num_cols = min(_MAX_MODULE_COLS, (len(ordered) + 3) // 4)
    col_size = (len(ordered) + num_cols - 1) // num_cols
    return [
        ordered[i : i + col_size]
        for i in range(0, len(ordered), col_size)
    ]


def _layout_positions(
    files: list[ManifestNode],
) -> tuple[dict[str, dict[str, int]], dict[str, dict[str, int]]]:
    """Deterministic 2D layered positions for modules, files, and declaration pills.

    Modules order left-to-right by dependency depth (breaking cross-module
    zig-zag cycles by minimum/average global file depth). Within each
    module, files spread left-to-right across rank columns by intra-module
    import depth and stack top-to-bottom within each rank column (ordered
    by parent Y-barycenter to reduce edge crossings). Inside each file,
    declaration pills order by `(intra_file_dep_depth, line_pos, name)`
    and wrap into balanced sub-columns with exact pill-width clearance so
    no two labels or boxes ever overlap.
    """
    by_name = {node.name: node for node in files}
    modules = sorted({node.module for node in files})

    global_file_levels = _longest_paths(
        sorted(by_name),
        lambda name: [p for p in sorted(by_name[name].parents) if p in by_name],
    )
    intra_file_levels = _longest_paths(
        sorted(by_name),
        lambda name: [
            p
            for p in sorted(by_name[name].parents)
            if p in by_name and by_name[p].module == by_name[name].module
        ],
    )

    # Module rank key from global file depths breaks cross-module zig-zag
    # import cycles in the natural upstream-to-downstream direction.
    mod_depth_key: dict[str, tuple[int, float, str]] = {}
    for module in modules:
        levels = [global_file_levels[n.name] for n in files if n.module == module]
        mod_depth_key[module] = (
            min(levels, default=0),
            sum(levels) / max(1, len(levels)),
            module,
        )

    module_parents: dict[str, set[str]] = {module: set() for module in modules}
    for node in files:
        for parent in node.parents:
            if parent in by_name and by_name[parent].module != node.module:
                module_parents[node.module].add(by_name[parent].module)

    ordered_modules_seed = sorted(modules, key=lambda m: mod_depth_key[m])
    module_levels = _longest_paths(
        ordered_modules_seed,
        lambda module: sorted(
            (
                p
                for p in module_parents[module]
                if module not in module_parents.get(p, set())
                or mod_depth_key[p] < mod_depth_key[module]
            ),
            key=lambda p: mod_depth_key[p],
        ),
    )

    positions: dict[str, dict[str, int]] = {}
    cells: dict[str, dict[str, int]] = {}
    file_center_y: dict[str, float] = {}

    cur_x = 0
    for module in sorted(
        modules, key=lambda name: (module_levels[name], mod_depth_key[name], name)
    ):
        module_start_x = cur_x
        module_members = [node for node in files if node.module == module]
        columns = _partition_module_columns(
            module_members, intra_file_levels, global_file_levels
        )

        col_x = module_start_x
        for col_index, col_nodes in enumerate(columns):
            if col_index > 0:
                # Re-sort same-rank members within the column by the Y
                # barycenter of their already-placed parent files.
                def _barycenter_key(
                    node: ManifestNode,
                ) -> tuple[int, int, int, float, str]:
                    placed = [
                        file_center_y[p]
                        for p in node.parents
                        if p in file_center_y
                    ]
                    bary = sum(placed) / len(placed) if placed else 0.0
                    return (
                        intra_file_levels[node.name],
                        global_file_levels[node.name],
                        0 if placed else 1,
                        bary,
                        node.name,
                    )

                col_nodes = sorted(col_nodes, key=_barycenter_key)

            y = _LAYOUT_TOP
            col_max_w = 0
            for member in col_nodes:
                ordered_decls = _order_file_declarations(member.declarations)
                title_w = len(dotted_stem_of(member)) * 8 + 36
                if not ordered_decls:
                    box_w = max(104, title_w)
                    box_h = _FILE_TITLE_H + 30 + _FILE_PAD_Y
                    cx = col_x + box_w // 2
                    cy = y + _FILE_TITLE_H + 15
                    positions[f"file:{member.name}"] = {"x": cx, "y": cy}
                    cells[f"file:{member.name}"] = {
                        "x1": col_x,
                        "y1": y,
                        "x2": col_x + box_w,
                        "y2": y + box_h,
                    }
                    file_center_y[member.name] = float(cy)
                    col_max_w = max(col_max_w, box_w)
                    y += box_h + _FILE_GAP_Y
                    continue

                num_subcols = _subcolumn_count(len(ordered_decls))
                rows_per_col = (len(ordered_decls) + num_subcols - 1) // num_subcols
                subcols = [
                    ordered_decls[i : i + rows_per_col]
                    for i in range(0, len(ordered_decls), rows_per_col)
                ]
                sc_widths = [
                    max(_pill_width(bare_name(d)) for d in sc) for sc in subcols
                ]
                pills_w = sum(sc_widths) + _SUBCOL_GAP * (len(subcols) - 1)
                max_rows = max(len(sc) for sc in subcols)
                pills_h = (max_rows - 1) * _DECL_ROW_STEP + _PILL_H
                box_w = max(pills_w + 2 * _FILE_PAD_X, title_w)
                box_h = _FILE_TITLE_H + pills_h + 2 * _FILE_PAD_Y

                first_subcol_left = col_x + (box_w - pills_w) // 2
                first_pill_cy = y + _FILE_TITLE_H + _FILE_PAD_Y + _PILL_H // 2

                subcol_left = first_subcol_left
                for sc, sc_w in zip(subcols, sc_widths):
                    pill_cx = subcol_left + sc_w // 2
                    for row_idx, decl in enumerate(sc):
                        pill_cy = first_pill_cy + row_idx * _DECL_ROW_STEP
                        positions[f"decl:{member.name}:{decl.name}"] = {
                            "x": pill_cx,
                            "y": pill_cy,
                        }
                    subcol_left += sc_w + _SUBCOL_GAP

                file_cx = col_x + box_w // 2
                file_cy = y + _FILE_TITLE_H + _FILE_PAD_Y + pills_h // 2
                positions[f"file:{member.name}"] = {"x": file_cx, "y": first_pill_cy}
                cells[f"file:{member.name}"] = {
                    "x1": col_x,
                    "y1": y,
                    "x2": col_x + box_w,
                    "y2": y + box_h,
                }
                file_center_y[member.name] = float(file_cy)
                col_max_w = max(col_max_w, box_w)
                y += box_h + _FILE_GAP_Y

            col_x += col_max_w + _RANK_GAP_X

        positions[f"module:{module}"] = {
            "x": module_start_x + _FILE_PAD_X,
            "y": _LAYOUT_TOP,
        }
        cur_x = max(col_x - _RANK_GAP_X, module_start_x) + _MODULE_PAD_X * 2 + _MODULE_GAP_X

    return positions, cells


def _indirect_ancestors_map(files: list[ManifestNode]) -> dict[str, set[str]]:
    """For each file, the set of ancestor files reachable in >= 2 import hops."""
    by_name = {node.name: node for node in files}
    direct_ancestors: dict[str, set[str]] = {}
    for node in files:
        visited: set[str] = set()
        stack = [p for p in node.parents if p in by_name]
        while stack:
            curr = stack.pop()
            if curr in visited:
                continue
            visited.add(curr)
            for gp in by_name[curr].parents:
                if gp in by_name and gp not in visited:
                    stack.append(gp)
        direct_ancestors[node.name] = visited

    indirect: dict[str, set[str]] = {}
    for node in files:
        ind: set[str] = set()
        for parent in node.parents:
            if parent in direct_ancestors:
                ind |= direct_ancestors[parent]
        indirect[node.name] = ind
    return indirect


def _effective_decl_states(
    files: list[ManifestNode],
) -> dict[tuple[str, str], str]:
    """Compute each declaration's state, treating non-verifiable kinds
    (defs, structures, instances, ...) as `done` (green) when they have
    been checked either directly (`checked_sig`) or as part of verifying
    a theorem in the same file or a downstream dependent declaration.

    `axbt verify` only stamps `verified_sig` on theorems/lemmas/examples,
    even though Lean's kernel elaborates and checks every definition and
    structure in the verified payload. Marking non-verifiable
    declarations in verified files (or depended on by verified/checked
    declarations) as `done` ensures verified files with definitions render
    green rather than orange.
    """
    raw_states: dict[tuple[str, str], str] = {}
    judged_deps: set[str] = set()
    file_has_verified: dict[str, bool] = {}

    for node in files:
        has_ver = any(
            bool(d.verified_sig or d.verified_at) for d in node.declarations
        )
        file_has_verified[node.name] = has_ver
        for decl in node.declarations:
            st = state_of(decl)
            raw_states[(node.name, decl.name)] = st
            if st in ("verified", "checked", "done"):
                for dep in decl.dependencies:
                    judged_deps.add(dep)
                    judged_deps.add(dep.rsplit(".", 1)[-1])

    effective: dict[tuple[str, str], str] = {}
    for node in files:
        for decl in node.declarations:
            st = raw_states[(node.name, decl.name)]
            if (
                st == "unchecked"
                and decl.kind not in _VERIFIABLE_KINDS
                and not decl.is_sorry
                and (
                    file_has_verified[node.name]
                    or decl.name in judged_deps
                    or decl.name.rsplit(".", 1)[-1] in judged_deps
                )
            ):
                st = "done"
            effective[(node.name, decl.name)] = st
    return effective


def _decl_counts_row_from_states(states: list[str]) -> str:
    """The `3 verified, 2 done, 1 checked, 0 unchecked` count line."""
    counts = {state: 0 for state in _STATES}
    for st in states:
        counts[st] += 1
    return (
        f"{counts['verified']} verified, {counts['done']} done, "
        f"{counts['checked']} checked (unverified), "
        f"{counts['unchecked']} unchecked"
    )


def build_graph_data(manifest: Manifest, files: list[ManifestNode]) -> dict[str, Any]:
    """Assemble the graph's data: compound nodes, edges, and counts.

    `files` is the rendered file set (expected: `rendered_nodes`' output
    — every member's dependency closure, so import edges' endpoints and
    the declaration dependencies' hosts are all present).
    """
    files = sorted(files, key=lambda node: node.name)
    modules = sorted({node.module for node in files})
    files_of_module: dict[str, list[ManifestNode]] = {module: [] for module in modules}

    edges: list[dict[str, Any]] = []
    edges_seen: set[tuple[str, str, str]] = set()
    effective_states = _effective_decl_states(files)

    # --- declare per-file data ------------------------------------------
    # Compounds must exist before their children in the elements list
    # (Cytoscape resolves containment), so the nodes list is assembled
    # modules-first: per-file data is computed below, then emitted.
    module_states: dict[str, list[str]] = {module: [] for module in modules}
    file_states_by_name: dict[str, list[str]] = {}
    file_nodes: list[dict[str, Any]] = []
    decl_nodes: list[dict[str, Any]] = []
    for node in files:
        files_of_module[node.module].append(node)
        file_members = _order_file_declarations(node.declarations)
        states = [effective_states[(node.name, decl.name)] for decl in file_members]
        file_states_by_name[node.name] = states
        module_states[node.module].extend(states)
        changed = node.status in ("new", "changed")
        file_label = dotted_stem_of(node) + (" " + _STAR if changed else "")
        decl_summary = _decl_counts_row_from_states(states)
        file_nodes.append(
            {
                "group": "file",
                "id": f"file:{node.name}",
                "label": file_label,
                "parent": f"module:{node.module}",
                "state": rollup_state(states),
                "changed": changed,
                "width": max(104, len(file_label) * 8 + 28),
                "path": node.path,
                "module": node.module,
                "status_text": _status_text(node),
                "decl_summary": decl_summary,
                "tooltip": _tooltip(
                    node.path,
                    [
                        ("module", node.module),
                        ("status", _status_text(node)),
                        ("md5", node.md5),
                        ("declarations", decl_summary),
                    ],
                ),
            }
        )
        for decl in file_members:
            label = bare_name(decl)
            decl_state = effective_states[(node.name, decl.name)]
            checked_str = _stamp_row(
                decl.checked_sig, decl.checked_at, decl.checked_request_id
            )
            verified_str = _stamp_row(
                decl.verified_sig, decl.verified_at, decl.verified_request_id
            )
            if checked_str == "—" and decl_state == "done":
                checked_str = "checked in verified closure"
            decl_nodes.append(
                {
                    "group": "declaration",
                    "id": f"decl:{node.name}:{decl.name}",
                    "label": label,
                    "full_name": decl.name,
                    "parent": f"file:{node.name}",
                    "state": decl_state,
                    "changed": changed,
                    "width": _pill_width(label),
                    # Shapes split by verifiability (see the template's
                    # style sheet): verifiable proof kinds render as
                    # ovals (ellipse), never-verifiable declarations
                    # (defs, instances, structures, ...) as solid
                    # sharp-cornered rectangles.
                    "kind": decl.kind,
                    "file_path": f"{node.path}:{decl.line_pos}",
                    "lines": f"{decl.line_pos}-{decl.end_line_pos}",
                    "is_sorry": decl.is_sorry,
                    "signature": decl.signature or "",
                    "checked_stamp": checked_str,
                    "verified_stamp": verified_str,
                    "external_deps": list(decl.external_dependencies),
                    "tooltip": _tooltip(
                        decl.name,
                        [
                            ("kind", decl.kind),
                            ("file", f"{node.path}:{decl.line_pos}"),
                            ("lines", f"{decl.line_pos}-{decl.end_line_pos}"),
                            ("sorry", "yes" if decl.is_sorry else "no"),
                            ("checked stamp", checked_str),
                            ("verified stamp", verified_str),
                        ],
                    ),
                }
            )

    # --- module compound nodes (their members' states are now known) ----
    module_nodes = [
        {
            "group": "module",
            "id": f"module:{module}",
            "label": module,
            "parent": None,
            "state": rollup_state(module_states[module]),
            "changed": False,
            "tooltip": _tooltip(
                module,
                [
                    (
                        dotted_stem_of(member),
                        f"{_status_text(member)}; {_decl_counts_row_from_states(file_states_by_name[member.name])}",
                    )
                    for member in files_of_module[module]
                ],
            ),
        }
        for module in modules
    ]
    #: Cytoscape requires compound parents to precede their children.
    nodes = [*module_nodes, *file_nodes, *decl_nodes]
    positions, cells = _layout_positions(files)
    for node in nodes:
        node["position"] = positions[node["id"]]
        if node["group"] == "file":
            node["cell"] = cells[node["id"]]

    # --- file-level import edges ----------------------------------------
    file_names = {node.name for node in files}
    indirect_ancestors = _indirect_ancestors_map(files)
    for node in files:
        for parent in sorted(node.parents):
            # Both endpoints are always in the rendered set (the closure
            # walk pulled every dependency in); the check is for direct
            # callers passing narrower file lists.
            if parent in file_names:
                key = (f"file:{parent}", f"file:{node.name}", "import")
                if key not in edges_seen:
                    edges_seen.add(key)
                    is_transitive = parent in indirect_ancestors.get(node.name, set())
                    edges.append(
                        {
                            "id": f"import:{parent}->{node.name}",
                            "source": key[0],
                            "target": key[1],
                            "kind": "import",
                            "transitive": is_transitive,
                            "tooltip": _tooltip(
                                "transitive import" if is_transitive else "import",
                                [("from", parent), ("into", node.name)],
                            ),
                        }
                    )

    # --- declaration-to-declaration edges --------------------------------
    # From the extraction dependency lists (the outcome-record work):
    # dependency -> dependent. Only edges resolving to exactly one
    # rendered declaration (by full name, then by unique bare-name
    # suffix) are drawn — ambiguous or external names are skipped,
    # never guessed.
    exact_ids: dict[str, list[str]] = {}
    suffix_ids: dict[str, list[str]] = {}
    for node in files:
        for decl in node.declarations:
            node_id = f"decl:{node.name}:{decl.name}"
            exact_ids.setdefault(decl.name, []).append(node_id)
            suffix_ids.setdefault(decl.name.rsplit(".", 1)[-1], []).append(node_id)

    for node in files:
        for decl in node.declarations:
            target = f"decl:{node.name}:{decl.name}"
            for dep in decl.dependencies:
                candidates = exact_ids.get(dep) or suffix_ids.get(
                    dep.rsplit(".", 1)[-1], []
                )
                if len(candidates) != 1 or candidates[0] == target:
                    continue
                key = (candidates[0], target, "depends")
                if key in edges_seen:
                    continue
                edges_seen.add(key)
                source_name = _decl_id_name(key[0])
                target_name = _decl_id_name(key[1])
                edges.append(
                    {
                        "id": f"dep:{key[0]}->{key[1]}",
                        "source": key[0],
                        "target": key[1],
                        "kind": "depends",
                        "transitive": False,
                        "tooltip": _tooltip(
                            "depends on",
                            [("declaration", source_name), ("used by", target_name)],
                        ),
                    }
                )

    declarations_total = sum(len(node.declarations) for node in files)
    return {
        "nodes": nodes,
        "edges": edges,
        "star": _STAR,
        "legend": [
            {"state": state, "text": _LEGEND_TEXT[state]}
            for state in (*_STATES, _EMPTY_STATE)
        ],
        "counts": {
            "modules": len(modules),
            "files": len(files),
            "declarations": declarations_total,
            "edges": len(edges),
        },
    }


def _stamp_row(sig: str | None, at: Any, request_id: str | None) -> str:
    """One stamp tier rendered for a tooltip (`—` when absent)."""
    if sig is None and at is None:
        return "—"
    parts = []
    if at is not None:
        parts.append(at.isoformat(timespec="seconds"))
    if request_id is not None:
        parts.append(f"request {request_id}")
    return "; ".join(parts)


def _embed(data: dict[str, Any]) -> str:
    """JSON-serialize `data` for safe embedding into a script tag.

    `<` and `>` are escaped to their `\\u003c`/`\\u003e` JSON escapes:
    the text stays exactly recoverable via `JSON.parse(textContent)`
    while incapable of forming a `</script>` (or any tag) anywhere in
    the page. Manifest-derived strings reach tooltip HTML only through
    `html.escape` (see `_tooltip`).
    """
    return json.dumps(data, ensure_ascii=True).replace("<", "\\u003c").replace(">", "\\u003e")


#: The in-page legend: one chip per state, shape legend, search bar,
#: edge toggles, and layout reset control.
#:
#: Verifiable declaration kinds render as rounded capsule pills;
#: everything else (defs, instances, structures, ...) renders as a
#: rectangular badge since `axbt verify` can never judge it.
_SHAPES_LEGEND = (
    '<div class="item shapes"><span class="glyph round"></span>'
    "theorem / lemma / example &mdash; verifiable (oval)"
    '<br><span class="glyph square"></span>'
    "other declarations (defs, structures, &hellip;) &mdash; never verifiable (rectangle)</div>"
)


def _legend_markup(legend: list[dict[str, str]], star: str) -> str:
    items = "".join(
        f'<div class="item"><span class="chip {entry["state"]}"></span>'
        f'{html.escape(entry["text"])}</div>'
        for entry in legend
    )
    note = html.escape(f"{star} marks files whose source is new or changed")
    search = (
        '<div class="search-wrap">'
        '<input type="search" id="search-nodes" placeholder="Search file or declaration…" autocomplete="off">'
        "</div>"
    )
    decl_checkbox = (
        '<label class="item ctrl"><input type="checkbox" id="toggle-decl-edges"> '
        "declaration dependency arrows (tick to show; clicking a declaration "
        "always reveals its dependency neighborhood)</label>"
    )
    trans_checkbox = (
        '<label class="item ctrl"><input type="checkbox" id="toggle-transitive-edges"> '
        "transitive file import arrows (tick to show shortcut imports alongside "
        "direct DAG edges)</label>"
    )
    reset = (
        '<button type="button" class="ctrl" id="reset-positions">'
        "reset layout</button>"
    )
    return (
        f'{search}<div class="title">color = outcome stamps only</div>{items}{_SHAPES_LEGEND}'
        f'{decl_checkbox}{trans_checkbox}{reset}<div class="note">{note}</div>'
        '<div id="inspector" style="display:none;"></div>'
    )


def _render_html(data: dict[str, Any], title: str) -> str:
    """Render the single-file HTML from prebuilt graph data."""
    counts = data["counts"]
    page_title = (
        f"{html.escape(title)} — {counts['files']} files, "
        f"{counts['declarations']} declarations, {counts['edges']} edges"
    )
    replacements = {
        "__AXBT_TITLE__": page_title,
        "__AXBT_LEGEND__": _legend_markup(data["legend"], data["star"]),
        "__AXBT_DATA__": _embed(data),
        "__AXBT_CDN__": CYTOSCAPE_URL,
        "__AXBT_INTEGRITY__": CYTOSCAPE_INTEGRITY,
    }
    page = _HTML_TEMPLATE
    for token, value in replacements.items():
        page = page.replace(token, value)
    return page


def graph_html(manifest: Manifest, files: list[ManifestNode], title: str = "axbt graph") -> str:
    """Render the single-file HTML (Cytoscape.js from the pinned CDN)."""
    return _render_html(build_graph_data(manifest, files), title)


def write_graph(
    manifest: Manifest,
    project_root: Path,
    files: list[ManifestNode],
    output: Path | None = None,
    title: str = "axbt graph",
) -> tuple[Path, dict[str, int]]:
    """Render and write the graph HTML, returning (path, counts).

    Counts are the graph's node/edge tallies for the command's report.
    `output=None` defaults to `.axbt/graph.html`; an explicit path is
    honored as given (parents are created as needed).
    """
    out = output if output is not None else graph_path(project_root)
    out.parent.mkdir(parents=True, exist_ok=True)
    data = build_graph_data(manifest, files)
    out.write_text(_render_html(data, title), encoding="utf-8")
    return out, data["counts"]


# --- The page template ---------------------------------------------------
# Plain string with token placeholders (no f-string): the HTML/CSS/JS
# braces are content, and the only interpolated pieces are the escaped
# title, legend, and the `_embed`ed JSON. The embedded data cannot
# contain any `<`, so it can neither break out of its script tag nor
# collide with the placeholder tokens.
_HTML_TEMPLATE = """<!doctype html>
<html>
<head>
<meta charset="utf-8">
<title>__AXBT_TITLE__</title>
<script src="__AXBT_CDN__" integrity="__AXBT_INTEGRITY__" crossorigin="anonymous"></script>
<style>
  body { margin: 0; height: 100vh; font-family: ui-sans-serif, system-ui, sans-serif; background: #0b101b; color: #dbe7f8; }
  #graph { position: fixed; inset: 0; }
  #legend { position: fixed; top: 10px; right: 10px; z-index: 10; background: rgba(15, 23, 42, 0.94);
            border: 1px solid #263859; border-radius: 10px; padding: 10px 13px; font-size: 12px; line-height: 1.75;
            max-width: 360px; max-height: calc(100vh - 28px); overflow-y: auto;
            box-shadow: 0 8px 24px rgba(0, 0, 0, 0.48); backdrop-filter: blur(6px); }
  #legend .title { font-weight: 600; margin-bottom: 2px; color: #f0f6fc; }
  #legend .item { line-height: 1.75; color: #c9d7ec; }
  #legend .search-wrap { margin-bottom: 8px; }
  #legend input[type="search"] { width: 100%; box-sizing: border-box; padding: 5px 9px; font-size: 12px;
                                 border: 1px solid #2e4369; border-radius: 6px; background: #131d31;
                                 color: #e6f0ff; outline: none; }
  #legend input[type="search"]::placeholder { color: #6e84a8; }
  #legend input[type="search"]:focus { border-color: #38bdf8; box-shadow: 0 0 0 2px rgba(56, 189, 248, 0.2); }
  #legend label.ctrl { display: block; margin: 5px 0 2px; line-height: 1.45; cursor: pointer; color: #b8cae4; }
  #legend label.ctrl input { vertical-align: -1px; margin-right: 5px; accent-color: #38bdf8; }
  #legend button.ctrl { display: block; width: 100%; margin: 6px 0 2px; font: 500 12px/1.5 ui-sans-serif, system-ui,
                        sans-serif; color: #d0def2; background: #16233b; border: 1px solid #2e4369; border-radius: 6px;
                        padding: 4px 8px; cursor: pointer; }
  #legend button.ctrl:hover { border-color: #4d73b3; background: #1e3050; color: #ffffff; }
  #legend .note { color: #8499bc; border-top: 1px solid #223250; margin-top: 6px; padding-top: 5px; font-size: 11.5px; }
  #legend .star { color: #ff6b6b; }
  .chip { display: inline-block; width: 11px; height: 11px; border-radius: 3px; margin-right: 6px; vertical-align: -.5px; }
  .chip.verified { background: #20c997; }
  .chip.done { background: #22b8cf; }
  .chip.checked { background: #f59f00; }
  .chip.unchecked { background: #ff6b35; }
  .chip.empty { background: #5c7099; }
  .glyph { display: inline-block; width: 20px; height: 11px; background: #182742;
           margin: 0 5px 0 1px; vertical-align: -1px; border: 1.5px solid #6c88b8; }
  .glyph.round { border-radius: 50%; }
  .glyph.square { border-radius: 0; }
  .shapes { margin: 4px 0; padding: 3px 0; border-top: 1px solid #223250; border-bottom: 1px solid #223250; }
  #inspector { border-top: 1px solid #263859; margin-top: 8px; padding-top: 8px; font-size: 12px; line-height: 1.5; }
  #inspector .insp-title { font-weight: 700; font-family: ui-monospace, monospace; font-size: 12.5px;
                           color: #f0f6fc; overflow-wrap: anywhere; margin-bottom: 4px; }
  #inspector .insp-meta { color: #94a9c9; font-size: 11.5px; margin-bottom: 4px; }
  #inspector pre.insp-sig { background: #090e19; border: 1px solid #233454; border-radius: 6px;
                            padding: 6px 8px; margin: 5px 0; font-family: ui-monospace, monospace;
                            color: #bae6fd; font-size: 11px; white-space: pre-wrap; overflow-wrap: anywhere;
                            max-height: 120px; overflow-y: auto; }
  #inspector .insp-sec { font-weight: 600; color: #8499bc; margin-top: 5px; font-size: 11px; text-transform: uppercase; letter-spacing: .03em; }
  #inspector .insp-chips { display: flex; flex-wrap: wrap; gap: 4px; margin-top: 3px; }
  #inspector .insp-chip { font-family: ui-monospace, monospace; font-size: 11px; background: #16233b;
                          border: 1px solid #2d436b; border-radius: 4px; padding: 1px 6px; cursor: pointer; color: #d0def2; }
  #inspector .insp-chip:hover { background: #1d3557; border-color: #38bdf8; color: #7dd3fc; }
  #tooltip { position: fixed; z-index: 20; display: none; max-width: 390px; background: #0f172a;
             border: 1px solid #2e4369; border-radius: 8px; padding: 8px 11px; font-size: 12px; line-height: 1.55;
             color: #e2ecf8; box-shadow: 0 8px 24px rgba(0, 0, 0, 0.6); pointer-events: none; }
  #tooltip .tt { font-weight: 600; margin-bottom: 3px; overflow-wrap: anywhere; font-family: ui-monospace, monospace; color: #f8fafc; }
  #tooltip .row { overflow-wrap: anywhere; }
  #tooltip .k { color: #7e95ba; display: inline-block; min-width: 92px; margin-right: 6px; }
  #tooltip code { font-family: ui-monospace, monospace; font-size: 11px; color: #bae6fd; }
</style>
</head>
<body>
<div id="graph"></div>
<div id="tooltip"></div>
<div id="legend">
__AXBT_LEGEND__
</div>
<script type="application/json" id="graph-data">__AXBT_DATA__</script>
<script>
(function () {
  "use strict";
  var payload = JSON.parse(document.getElementById("graph-data").textContent);
  var tooltip = document.getElementById("tooltip");
  var inspector = document.getElementById("inspector");

  var cy = window.cytoscape({
    container: document.getElementById("graph"),
    boxSelectionEnabled: false,
    elements: payload.nodes
      .map(function (node) {
        return { data: node, classes: node.state, position: node.position };
      })
      .concat(
        payload.edges.map(function (edge) {
          var cls = edge.kind + (edge.transitive ? " transitive" : "");
          return { data: edge, classes: cls };
        })
      ),
    style: [
      { selector: "node", style: {
        label: "data(label)", "font-size": 11, "text-valign": "center", "text-halign": "center",
        color: "#e6f0ff", "font-family": "ui-sans-serif, system-ui, sans-serif", shape: "ellipse" } },
      { selector: "node[group='declaration']", style: {
        width: "data(width)", height: 28, "font-size": 11,
        "font-family": "ui-monospace, SFMono-Regular, Menlo, monospace",
        "text-valign": "center", "text-halign": "center",
        "border-style": "solid",
        shape: "rectangle" } },
      { selector: "node[kind='theorem'], node[kind='lemma'], node[kind='example']", style: {
        "border-style": "solid",
        shape: "ellipse" } },
      { selector: "node[group='file']", style: {
        shape: "roundrectangle", width: "data(width)", height: 28, "font-size": 12, "font-weight": 600 } },
      { selector: "node[state='verified']", style: {
        "background-color": "#0e3a2f", "border-color": "#20c997", "border-width": 1.8, color: "#d3f9d8" } },
      { selector: "node[state='done']", style: {
        "background-color": "#0c324a", "border-color": "#22b8cf", "border-width": 2, color: "#c5f6fa" } },
      { selector: "node[state='checked']", style: {
        "background-color": "#3b2a0a", "border-color": "#f59f00", "border-width": 1.8, color: "#ffec99" } },
      { selector: "node[state='unchecked']", style: {
        "background-color": "#3d1a11", "border-color": "#ff6b35", "border-width": 1.8, color: "#ffd8a8" } },
      { selector: "node[state='empty']", style: {
        "background-color": "#19253a", "border-color": "#5c7099", "border-width": 1.4, color: "#a5b8d4" } },
      { selector: "edge", style: {
        width: 1.5, "curve-style": "bezier", "line-color": "#4f6d9a", "target-arrow-color": "#4f6d9a",
        "target-arrow-shape": "triangle", "arrow-scale": 0.75, opacity: 0.84 } },
      { selector: "edge.transitive", style: {
        width: 1.1, "line-style": "dotted", opacity: 0.42 } },
      { selector: "edge[kind='depends']", style: {
        "line-color": "#60a5fa", "target-arrow-color": "#60a5fa", "line-style": "dashed", width: 1.4 } },
      { selector: "node:parent", style: {
        shape: "roundrectangle", "font-size": 12, "font-weight": 600, color: "#d0def2",
        "background-color": "#131d31", "background-opacity": 0.6, "border-color": "#2b3e63", "border-width": 1.3,
        padding: "16px",
        "text-valign": "top", "text-halign": "center", "text-margin-y": -6,
        "text-background-color": "#0b101b", "text-background-opacity": 0.9,
        "text-background-padding": "3px", "text-background-shape": "roundrectangle" } },
      { selector: "node:parent[group='module']", style: {
        "font-size": 14, "font-weight": 700, color: "#e6f0ff", padding: "24px", "text-margin-y": -8,
        "background-color": "#111a2e", "background-opacity": 0.5, "border-color": "#314873", "border-width": 1.6 } },
      { selector: "node:parent[group='file'][state='verified'], node:parent[group='file'][state='done']", style: {
        "background-color": "#0c2b26", "background-opacity": 0.45, "border-color": "#1aa179", "border-width": 1.5 } },
      { selector: "node:parent[group='file'][state='checked']", style: {
        "background-color": "#2e230a", "background-opacity": 0.45, "border-color": "#d99b16", "border-width": 1.5 } },
      { selector: "node:parent[group='file'][state='unchecked']", style: {
        "background-color": "#301610", "background-opacity": 0.45, "border-color": "#e8590c", "border-width": 1.5 } },
      { selector: "node:parent[group='file'][state='empty']", style: {
        "background-color": "#162136", "background-opacity": 0.45, "border-color": "#4a5f85" } },
      { selector: ".highlighted", style: { "border-color": "#38bdf8", "border-width": 2.5 } },
      { selector: ".selected-node", style: { "border-color": "#7dd3fc", "border-width": 3 } },
      { selector: "edge.highlighted", style: { width: 2.4, "line-color": "#38bdf8", "target-arrow-color": "#38bdf8", opacity: 1 } },
      { selector: ".dimmed", style: { opacity: 0.2 } },
      { selector: "edge.hidden", style: { display: "none" } }
    ],
    layout: {
      // All coordinates are computed deterministically at build time
      // (2D layered rank columns + multi-column pill grids).
      name: "preset", padding: 40, fit: true
    }
  });

  // Copy initial preset positions so reset restores the exact build-time layout.
  var initialPositions = {};
  cy.nodes().forEach(function (node) {
    if (!node.isParent()) {
      initialPositions[node.id()] = { x: node.position("x"), y: node.position("y") };
    }
  });

  function spreadFileClusters() {
    // Layout is deterministic at build time; retained as a no-op hook
    // called by the reset button before restoring preset coordinates.
  }

  // -- interaction state -------------------------------------------------
  var marked = [];
  var declToggle = document.getElementById("toggle-decl-edges");
  var transToggle = document.getElementById("toggle-transitive-edges");
  var searchInput = document.getElementById("search-nodes");
  var depsHidden = declToggle ? !declToggle.checked : true;
  var transHidden = transToggle ? !transToggle.checked : true;

  function refreshEdgeVisibility() {
    cy.batch(function () {
      cy.edges('[kind = "depends"]').forEach(function (edge) {
        var revealed = marked.indexOf(edge) !== -1;
        edge.toggleClass("hidden", depsHidden && !revealed);
      });
      cy.edges('edge.transitive').forEach(function (edge) {
        var revealed = marked.indexOf(edge) !== -1;
        edge.toggleClass("hidden", transHidden && !revealed);
      });
    });
  }

  function clearMark() {
    cy.batch(function () {
      cy.elements().removeClass("highlighted selected-node dimmed");
    });
    marked = [];
    if (inspector) { inspector.style.display = "none"; inspector.innerHTML = ""; }
    refreshEdgeVisibility();
  }

  function transitiveCone(seed, edgeKind) {
    var coneNodes = {};
    var coneEdges = [];
    coneNodes[seed.id()] = seed;

    // Upstream walk (predecessors along edgeKind)
    var upQueue = [seed];
    while (upQueue.length > 0) {
      var curr = upQueue.pop();
      curr.incomers('edge[kind = "' + edgeKind + '"]').forEach(function (edge) {
        coneEdges.push(edge);
        var src = edge.source();
        if (!coneNodes[src.id()]) {
          coneNodes[src.id()] = src;
          upQueue.push(src);
        }
      });
    }

    // Downstream walk (successors along edgeKind)
    var downQueue = [seed];
    while (downQueue.length > 0) {
      var currDown = downQueue.pop();
      currDown.outgoers('edge[kind = "' + edgeKind + '"]').forEach(function (edge) {
        coneEdges.push(edge);
        var tgt = edge.target();
        if (!coneNodes[tgt.id()]) {
          coneNodes[tgt.id()] = tgt;
          downQueue.push(tgt);
        }
      });
    }

    var result = [];
    Object.keys(coneNodes).forEach(function (id) { result.push(coneNodes[id]); });
    for (var i = 0; i < coneEdges.length; i++) { result.push(coneEdges[i]); }
    return result;
  }

  function escapeHtml(str) {
    return String(str == null ? "" : str)
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;")
      .replace(/'/g, "&#39;");
  }

  function renderInspector(node) {
    if (!inspector) { return; }
    var d = node.data();
    var htmlParts = [];
    if (d.group === "declaration") {
      htmlParts.push('<div class="insp-title">' + escapeHtml(d.full_name || d.label) + '</div>');
      htmlParts.push(
        '<div class="insp-meta"><span class="chip ' + escapeHtml(d.state) + '"></span>' +
        '<strong>' + escapeHtml(d.kind) + '</strong> &middot; ' +
        escapeHtml(d.file_path) + ' (lines ' + escapeHtml(d.lines) + ')' +
        (d.is_sorry ? ' &middot; <strong style="color:#c92a2a;">sorry</strong>' : '') +
        '</div>'
      );
      if (d.signature) {
        htmlParts.push('<pre class="insp-sig">' + escapeHtml(d.signature) + '</pre>');
      }
      var upDecls = node.incomers('edge[kind = "depends"]').sources();
      var downDecls = node.outgoers('edge[kind = "depends"]').targets();
      if (upDecls.length > 0) {
        htmlParts.push('<div class="insp-sec">Depends on (' + upDecls.length + ')</div><div class="insp-chips">');
        upDecls.forEach(function (u) {
          htmlParts.push('<span class="insp-chip" data-target-id="' + escapeHtml(u.id()) + '">' + escapeHtml(u.data("label")) + '</span>');
        });
        htmlParts.push('</div>');
      }
      if (downDecls.length > 0) {
        htmlParts.push('<div class="insp-sec">Used by (' + downDecls.length + ')</div><div class="insp-chips">');
        downDecls.forEach(function (dn) {
          htmlParts.push('<span class="insp-chip" data-target-id="' + escapeHtml(dn.id()) + '">' + escapeHtml(dn.data("label")) + '</span>');
        });
        htmlParts.push('</div>');
      }
    } else if (d.group === "file") {
      htmlParts.push('<div class="insp-title">' + escapeHtml(d.path || d.label) + '</div>');
      htmlParts.push(
        '<div class="insp-meta"><span class="chip ' + escapeHtml(d.state) + '"></span>' +
        'module <strong>' + escapeHtml(d.module) + '</strong> &middot; ' +
        escapeHtml(d.status_text) + '<br>' + escapeHtml(d.decl_summary) + '</div>'
      );
      var upFiles = node.incomers('edge[kind = "import"]').sources();
      var downFiles = node.outgoers('edge[kind = "import"]').targets();
      if (upFiles.length > 0) {
        htmlParts.push('<div class="insp-sec">Imports (' + upFiles.length + ')</div><div class="insp-chips">');
        upFiles.forEach(function (u) {
          htmlParts.push('<span class="insp-chip" data-target-id="' + escapeHtml(u.id()) + '">' + escapeHtml(u.data("label")) + '</span>');
        });
        htmlParts.push('</div>');
      }
      if (downFiles.length > 0) {
        htmlParts.push('<div class="insp-sec">Imported by (' + downFiles.length + ')</div><div class="insp-chips">');
        downFiles.forEach(function (dn) {
          htmlParts.push('<span class="insp-chip" data-target-id="' + escapeHtml(dn.id()) + '">' + escapeHtml(dn.data("label")) + '</span>');
        });
        htmlParts.push('</div>');
      }
    } else {
      inspector.style.display = "none";
      return;
    }
    inspector.innerHTML = htmlParts.join("");
    inspector.style.display = "block";
    var chips = inspector.querySelectorAll(".insp-chip");
    for (var i = 0; i < chips.length; i++) {
      chips[i].addEventListener("click", function () {
        var targetId = this.getAttribute("data-target-id");
        var targetNode = cy.getElementById(targetId);
        if (targetNode && targetNode.length > 0) {
          selectElement(targetNode);
        }
      });
    }
  }

  function selectElement(target) {
    clearMark();
    if (!target || target === cy) { return; }
    var group = target.data && target.data("group");
    if (group === "declaration") {
      marked = transitiveCone(target, "depends");
    } else if (group === "file") {
      marked = transitiveCone(target, "import");
    } else {
      marked = target.closedNeighborhood().toArray();
    }
    cy.batch(function () {
      for (var i = 0; i < marked.length; i++) {
        marked[i].addClass("highlighted");
      }
      if (target.isNode && target.isNode()) {
        target.addClass("selected-node");
        renderInspector(target);
      }
    });
    refreshEdgeVisibility();
  }

  function moveTooltip(e) {
    var ev = e.originalEvent;
    if (!ev || typeof ev.clientX !== "number") { return; }
    tooltip.style.left = ev.clientX + 14 + "px";
    tooltip.style.top = ev.clientY + 14 + "px";
  }

  if (declToggle) {
    declToggle.addEventListener("change", function () {
      depsHidden = !declToggle.checked;
      clearMark();
    });
  }
  if (transToggle) {
    transToggle.addEventListener("change", function () {
      transHidden = !transToggle.checked;
      clearMark();
    });
  }
  if (searchInput) {
    searchInput.addEventListener("input", function () {
      var q = searchInput.value.trim().toLowerCase();
      if (!q) {
        clearMark();
        return;
      }
      var matches = [];
      cy.nodes().forEach(function (n) {
        var g = n.data("group");
        if (g !== "declaration" && g !== "file") { return; }
        var text = ((n.data("full_name") || "") + " " + (n.data("label") || "") + " " + (n.data("path") || "")).toLowerCase();
        if (text.indexOf(q) !== -1) {
          matches.push(n);
        }
      });
      cy.batch(function () {
        cy.elements().removeClass("highlighted selected-node dimmed");
        if (matches.length > 0) {
          cy.nodes('[group = "declaration"]').addClass("dimmed");
          for (var i = 0; i < matches.length; i++) {
            matches[i].removeClass("dimmed").addClass("highlighted");
          }
        }
      });
    });
    searchInput.addEventListener("keydown", function (ev) {
      if (ev.key === "Enter") {
        var q = searchInput.value.trim().toLowerCase();
        if (!q) { return; }
        var first = null;
        cy.nodes().forEach(function (n) {
          if (first) { return; }
          var g = n.data("group");
          if (g !== "declaration" && g !== "file") { return; }
          var text = ((n.data("full_name") || "") + " " + (n.data("label") || "") + " " + (n.data("path") || "")).toLowerCase();
          if (text.indexOf(q) !== -1) { first = n; }
        });
        if (first) {
          selectElement(first);
          cy.animate({ center: { eles: first }, duration: 220 });
        }
      }
    });
  }

  cy.on("tap", function (e) {
    if (e.target === cy) { clearMark(); return; }
    selectElement(e.target);
  });
  cy.on("mouseover", "node", function (e) {
    tooltip.innerHTML = e.target.data("tooltip") || "";
    tooltip.style.display = "block";
    moveTooltip(e);
  });
  cy.on("mousemove", "node", function (e) { moveTooltip(e); });
  cy.on("mouseout", "node", function () { tooltip.style.display = "none"; });

  var resetButton = document.getElementById("reset-positions");
  if (resetButton) {
    resetButton.addEventListener("click", function () {
      if (searchInput) { searchInput.value = ""; }
      clearMark();
      cy.batch(function () {
        cy.nodes().forEach(function (node) {
          var preset = initialPositions[node.id()];
          if (preset !== undefined) { node.position(preset); }
        });
      });
      spreadFileClusters();
      cy.fit(undefined, 40);
    });
  }

  refreshEdgeVisibility();
  spreadFileClusters();
  cy.fit(undefined, 40);

  cy.on("resize", function () { cy.fit(undefined, 40); });
})();
</script>
</body>
</html>
"""
