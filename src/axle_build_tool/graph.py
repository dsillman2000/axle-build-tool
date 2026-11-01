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
  Declaration kinds that can never verify (defs, ...) land here too,
  which is exactly their terminal state ("done on their own tier").
- `unchecked` (orange) — neither stamp: never judged by a full,
  unstubbed payload.

Container nodes (files, modules) roll up to the weakest constituent
declaration state (orange > yellow > green); containers with no
extracted declarations (declaration-free import-only files) are
`empty` (grey). Manifests written before the stamp work degrade
automatically to the verified-vs-orange palette — no stub-and-hope
inference anywhere.

The page is interactive (pan/zoom, hover tooltips, click-to-highlight
a node's neighborhood) from the CDN script alone. Data reaches the
page as JSON embedded in a `<script type="application/json">` block:
`json.dumps` with every `<`/`>` escaped to `\\u003c`/`\\u003e` — valid
JSON that cannot form `</script>` (or any tag) in the page — and every
manifest-derived string is escaped into tooltip markup with
`html.escape`. Names are never interpolated into HTML raw.
"""

from __future__ import annotations

import html
import json
from pathlib import Path
from typing import Any

from axle_build_tool.config import CACHE_DIRNAME
from axle_build_tool.manifest import Manifest, ManifestNode
from axle_build_tool.payloads import dotted_stem_of
from axle_build_tool.stubbing import bare_name

#: Generated graph artifacts live in the cache alongside the payloads.
GRAPH_FILENAME = "graph.html"

#: The page's scripts from a CDN (pinned versions; SRI hashes computed
#: from the served bytes) — never bundled into axbt, never fetched by
#: it. Load order matters: `cytoscape-fcose`'s UMD build binds its
#: dependencies by global name, so `layout-base` and `cose-base` must
#: precede it; fcose (the compound-aware force layout) spreads each
#: file's cluster.
CYTOSCAPE_URL = "https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.31.0/cytoscape.min.js"
CYTOSCAPE_INTEGRITY = (
    "sha512-SRHUEtWi7EdmapdotitmlD7tNoeRXCtll4Y0yl2YYJB+m+IuIEvvHjZ7V34/k5ZFBtMN/"
    "uehjaerdJGr7hgt1g=="
)
LAYOUT_BASE_URL = "https://cdn.jsdelivr.net/npm/layout-base@2.0.1/layout-base.js"
LAYOUT_BASE_INTEGRITY = (
    "sha512-3QjpeCBhZ3yEArsOt12EqgfXoQjlH9RhU2o+Y7zu2G3COjWD4kbcwY0pd9ExrIwGB0RT69BEhQIKrnu2VQXhvQ=="
)
COSE_BASE_URL = "https://cdn.jsdelivr.net/npm/cose-base@2.2.0/cose-base.js"
COSE_BASE_INTEGRITY = (
    "sha512-wxZH0Y/3GE1Xx2eC0b++JqX7aLO96mykVCuzEpJQPyYXT4ZoGROZmMlcXpfSLgqW57yznXw36jB8DCdH3bjzEg=="
)
FCOSE_URL = "https://cdn.jsdelivr.net/npm/cytoscape-fcose@2.2.0/cytoscape-fcose.js"
FCOSE_INTEGRITY = (
    "sha512-RJqr1GzAaYbgpUAEvIzqTNMSTaVsAjcrK2JWOQ1suACA1LS4QSqhNelbAi+BT0GAeO4+nqVl19JaRA8R8TsDUw=="
)

#: weakest -> strongest; containers roll up to the weakest constituent.
_STATES = ["unchecked", "checked", "verified"]
_EMPTY_STATE = "empty"

_LEGEND_TEXT = {
    "verified": "verified — has a kernel verification stamp",
    "checked": "checked — passed typecheck, awaiting kernel verification",
    "unchecked": "unchecked — never judged by a full, unstubbed check",
    _EMPTY_STATE: "empty — a file/module with no declarations extracted",
}

#: The red-asterisk marker for files whose source is new or changed.
_STAR = "\u2731"


def graph_path(project_root: Path) -> Path:
    """The default graph output path: `.axbt/graph.html`."""
    return project_root / CACHE_DIRNAME / GRAPH_FILENAME


def state_of(declaration: Any) -> str:
    """A declaration's pipeline state, keyed strictly on its stamps."""
    if declaration.verified_sig or declaration.verified_at:
        return "verified"
    if declaration.checked_sig or declaration.checked_at:
        return "checked"
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
    by_name = manifest.by_name()
    rendered: dict[str, ManifestNode] = {}

    def visit(node: ManifestNode) -> None:
        if node.name in rendered:
            return
        rendered[node.name] = node
        for parent_name in sorted(node.parents):
            visit(by_name[parent_name])

    for node in selected:
        visit(node)
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
        f"{counts['verified']} verified, {counts['checked']} checked (unverified), "
        f"{counts['unchecked']} unchecked"
    )


def _status_text(node: ManifestNode) -> str:
    """The file's diff status with its marker if changed."""
    return f"{node.status} {_STAR}" if node.status in ("new", "changed") else node.status


#: Layout constants (pixels). Columns per module: `_CELL_W` is the
#: reserved per-module width (labels may bleed into the `_COLUMN_GAP`
#: gutter), `_DOT_X` the declaration dot's inset, `_HEADER_H` the
#: space above the first declaration row of a file cluster. Each file's
#: cluster also emits a `cell` rectangle (`_CELL_SPREAD` wide to the
#: left) that the page's per-file euler layout may spread its
#: declarations through.
_CELL_W = 280
_CELL_SPREAD = 24
_COLUMN_GAP = 110
_COLUMN_PAD = 10
_LAYOUT_TOP = 40
_DOT_X = 26
_DECL_ROW = 26
_HEADER_H = 34
_CLUSTER_GAP = 42


def _layout_positions(files: list[ManifestNode]) -> dict[str, dict[str, int]]:
    """Deterministic module-column positions, computed at build time.

    The page's JS layouting covers only the inside of file clusters
    (per-file euler, confined to the emitted `cell` rectangles); the
    macro structure is fixed here: each module is a column (modules
    ordered left-to-right by dependency depth, so cross-module edges
    flow left-to-right), files stack top-to-bottom within their module
    ordered by internal import depth, and the file's declarations get
    preset positions seeding the per-file force pass. Returns
    (element id -> (x, y), file id -> cell rect); file compounds' own
    positions only matter when a file has no declarations (otherwise
    the renderer surrounds them with their members).
    """
    by_name = {node.name: node for node in files}
    modules = sorted({node.module for node in files})

    def file_level(name: str) -> int:
        """Longest import path above the file, within its column."""
        parents = by_name[name].parents
        return 1 + max((file_level(p) for p in parents if p in by_name), default=-1)

    # Column order: longest-path layering of the module DAG induced by
    # the files' imports (dependencies first, left to right).
    module_parents: dict[str, set[str]] = {module: set() for module in modules}
    for node in files:
        for parent in node.parents:
            if parent in by_name:
                module_parents[node.module].add(by_name[parent].module)

    def module_level(module: str) -> int:
        return 1 + max(
            (
                module_level(parent)
                for parent in module_parents[module]
                if parent != module
            ),
            default=-1,
        )

    positions: dict[str, dict[str, int]] = {}
    cells: dict[str, dict[str, int]] = {}
    x = 0
    for module in sorted(modules, key=lambda name: (module_level(name), name)):
        column_x = x
        y = _LAYOUT_TOP
        members = sorted(
            (node for node in files if node.module == module),
            key=lambda node: (file_level(node.name), node.name),
        )
        for member in members:
            members_decls = sorted(member.declarations, key=lambda decl: decl.name)
            cluster_h = _HEADER_H + _DECL_ROW * max(1, len(members_decls))
            dot_x = column_x + _DOT_X
            dot_y = y + _HEADER_H
            positions[f"file:{member.name}"] = {"x": dot_x, "y": dot_y}
            for index, decl in enumerate(members_decls):
                positions[f"decl:{member.name}:{decl.name}"] = {
                    "x": dot_x,
                    "y": dot_y + _DECL_ROW * index,
                }
            # The cell the page's per-file euler layout may spread this
            # file's declarations through: the preset stack seeds it,
            # the cell bounds confine it ((x1, y1)-(x2, y2) in page
            # coordinates).
            cells[f"file:{member.name}"] = {
                "x1": dot_x - _CELL_SPREAD,
                "y1": y + 4,
                "x2": column_x + _CELL_W - 8,
                "y2": y + cluster_h - 4,
            }
            y += cluster_h + _CLUSTER_GAP
        # Module compounds' positions are derived from their files by
        # the renderer; an (impossible) empty module column would still
        # need a coordinate.
        positions[f"module:{module}"] = {"x": column_x + _DOT_X, "y": _LAYOUT_TOP}
        x += _CELL_W + _COLUMN_GAP
    return positions, cells


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

    # --- declare per-file data ------------------------------------------
    # Compounds must exist before their children in the elements list
    # (Cytoscape resolves containment), so the nodes bitmask is assembled
    # modules-first: per-file data is computed below, then emitted.
    module_states: dict[str, list[str]] = {module: [] for module in modules}
    file_nodes: list[dict[str, Any]] = []
    decl_nodes: list[dict[str, Any]] = []
    for node in files:
        files_of_module[node.module].append(node)
        file_members = sorted(node.declarations, key=lambda decl: decl.name)
        states = [state_of(decl) for decl in file_members]
        module_states[node.module].extend(states)
        changed = node.status in ("new", "changed")
        file_label = dotted_stem_of(node) + (" " + _STAR if changed else "")
        file_nodes.append(
            {
                "group": "file",
                "id": f"file:{node.name}",
                "label": file_label,
                "parent": f"module:{node.module}",
                "state": rollup_state(states),
                "changed": changed,
                "tooltip": _tooltip(
                    node.path,
                    [
                        ("module", node.module),
                        ("status", _status_text(node)),
                        ("md5", node.md5),
                        ("declarations", _decl_counts_row(file_members)),
                    ],
                ),
            }
        )
        for decl in file_members:
            decl_nodes.append(
                {
                    "group": "declaration",
                    "id": f"decl:{node.name}:{decl.name}",
                    "label": bare_name(decl),
                    "parent": f"file:{node.name}",
                    "state": state_of(decl),
                    "changed": changed,
                    "tooltip": _tooltip(
                        decl.name,
                        [
                            ("kind", decl.kind),
                            ("file", f"{node.path}:{decl.line_pos}"),
                            ("lines", f"{decl.line_pos}-{decl.end_line_pos}"),
                            ("sorry", "yes" if decl.is_sorry else "no"),
                            ("checked stamp", _stamp_row(decl.checked_sig, decl.checked_at, decl.checked_request_id)),
                            ("verified stamp", _stamp_row(decl.verified_sig, decl.verified_at, decl.verified_request_id)),
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
                        f"{_status_text(member)}; {_decl_counts_row(member.declarations)}",
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
    for node in files:
        for parent in sorted(node.parents):
            # Both endpoints are always in the rendered set (the closure
            # walk pulled every dependency in); the check is for direct
            # callers passing narrower file lists.
            if parent in file_names:
                key = (f"file:{parent}", f"file:{node.name}", "import")
                if key not in edges_seen:
                    edges_seen.add(key)
                    edges.append(
                        {
                            "id": f"import:{parent}->{node.name}",
                            "source": key[0],
                            "target": key[1],
                            "kind": "import",
                            "tooltip": _tooltip(
                                "import", [("from", parent), ("into", node.name)]
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


def _legend_markup(legend: list[dict[str, str]], star: str) -> str:
    """The in-page legend: one chip per state."""
    items = "".join(
        f'<div class="item"><span class="chip {entry["state"]}"></span>'
        f'{html.escape(entry["text"])}</div>'
        for entry in legend
    )
    note = html.escape(f"{star} marks files whose source is new or changed")
    return f'<div class="title">color = outcome stamps only</div>{items}<div class="note">{note}</div>'


def graph_html(manifest: Manifest, files: list[ManifestNode], title: str = "axbt graph") -> str:
    """Render the single-file HTML (Cytoscape.js from the pinned CDN)."""
    data = build_graph_data(manifest, files)
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
        "__AXBT_LAYOUT_BASE__": LAYOUT_BASE_URL,
        "__AXBT_LAYOUT_BASE_INTEGRITY__": LAYOUT_BASE_INTEGRITY,
        "__AXBT_COSE_BASE__": COSE_BASE_URL,
        "__AXBT_COSE_BASE_INTEGRITY__": COSE_BASE_INTEGRITY,
        "__AXBT_FCOSE__": FCOSE_URL,
        "__AXBT_FCOSE_INTEGRITY__": FCOSE_INTEGRITY,
    }
    page = _HTML_TEMPLATE
    for token, value in replacements.items():
        page = page.replace(token, value)
    return page


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
    html_text = graph_html(manifest, files, title=title)
    counts = build_graph_data(manifest, files)["counts"]
    out.write_text(html_text, encoding="utf-8")
    return out, counts


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
<script src="__AXBT_LAYOUT_BASE__" integrity="__AXBT_LAYOUT_BASE_INTEGRITY__" crossorigin="anonymous"></script>
<script src="__AXBT_COSE_BASE__" integrity="__AXBT_COSE_BASE_INTEGRITY__" crossorigin="anonymous"></script>
<script src="__AXBT_CDN__" integrity="__AXBT_INTEGRITY__" crossorigin="anonymous"></script>
<script src="__AXBT_FCOSE__" integrity="__AXBT_FCOSE_INTEGRITY__" crossorigin="anonymous"></script>
<style>
  body { margin: 0; height: 100vh; font-family: ui-sans-serif, system-ui, sans-serif; background: #faf8f4; }
  #graph { position: fixed; inset: 0; }
  #legend { position: fixed; top: 10px; right: 10px; z-index: 10; background: rgba(255,255,255,.93);
            border: 1px solid #d6d1c8; border-radius: 8px; padding: 8px 12px; font-size: 12px; line-height: 1.9;
            max-width: 340px; }
  #legend .title { font-weight: 600; margin-bottom: 2px; }
  #legend .note { color: #6b6257; border-top: 1px solid #e2ddd4; margin-top: 4px; padding-top: 4px; }
  #legend .star { color: #c92a2a; }
  .chip { display: inline-block; width: 11px; height: 11px; border-radius: 3px; margin-right: 6px; vertical-align: -.5px; }
  .chip.verified { background: #2f9e44; }
  .chip.checked { background: #f2b705; }
  .chip.unchecked { background: #e8590c; }
  .chip.empty { background: #c8c3bc; }
  #tooltip { position: fixed; z-index: 20; display: none; max-width: 380px; background: #fffdf9;
             border: 1px solid #d6d1c8; border-radius: 8px; padding: 8px 11px; font-size: 12px; line-height: 1.55;
             box-shadow: 0 6px 16px rgba(0,0,0,.12); pointer-events: none; }
  #tooltip .tt { font-weight: 600; margin-bottom: 3px; overflow-wrap: anywhere; font-family: ui-monospace, monospace; }
  #tooltip .row { overflow-wrap: anywhere; }
  #tooltip .k { color: #6b6257; display: inline-block; min-width: 92px; margin-right: 6px; }
  #tooltip code { font-family: ui-monospace, monospace; font-size: 11px; }
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

  if (window.cytoscapeFcose) { window.cytoscape.use(window.cytoscapeFcose); }

  var cy = window.cytoscape({
    container: document.getElementById("graph"),
    boxSelectionEnabled: false,
    autoungrabify: true,
    elements: payload.nodes
      .map(function (node) {
        return { data: node, classes: node.state, position: node.position };
      })
      .concat(
        payload.edges.map(function (edge) {
          return { data: edge, classes: edge.kind };
        })
      ),
    style: [
      { selector: "node", style: {
        label: "data(label)", "font-size": 11, "text-valign": "center", "text-halign": "center",
        color: "#212529", "text-background-color": "#ffffff", "text-background-opacity": 0.75,
        "text-background-padding": "2px", "text-background-shape": "roundrectangle",
        "font-family": "ui-sans-serif, system-ui, sans-serif", shape: "ellipse" } },
      { selector: "node[group='declaration']", style: {
        width: 12, height: 12, "font-size": 11,
        "text-valign": "center", "text-halign": "right", "text-margin-x": 12 } },
      { selector: "node[group='file']", style: { shape: "roundrectangle", width: 26, height: 26, "font-size": 12 } },
      { selector: "node[state='verified']", style: { "background-color": "#2f9e44", "border-color": "#237032", "border-width": 1 } },
      { selector: "node[state='checked']", style: { "background-color": "#f2b705", "border-color": "#c58a00", "border-width": 1 } },
      { selector: "node[state='unchecked']", style: { "background-color": "#e8590c", "border-color": "#b03a00", "border-width": 1 } },
      { selector: "node[state='empty']", style: { "background-color": "#c8c3bc", "border-color": "#9b958c", "border-width": 1, color: "#55504a" } },
      { selector: "edge", style: {
        width: 1.4, "curve-style": "bezier", "line-color": "#9c938a", "target-arrow-color": "#9c938a",
        "target-arrow-shape": "triangle", "arrow-scale": 0.7, opacity: 0.85 } },
      { selector: "edge[kind='depends']", style: { "line-color": "#4c7ef3", "target-arrow-color": "#4c7ef3", "line-style": "dashed" } },
      { selector: "node:parent", style: {
        shape: "roundrectangle", "font-size": 12, "font-weight": 600, color: "#4a443c",
        "background-color": "#eae4da", "background-opacity": 0.4, "border-color": "#cdc5b8", "border-width": 1,
        "text-valign": "top", "text-halign": "left", "text-margin-x": 10, "text-margin-y": 4 } },
      { selector: "node:parent[state='verified']", style: { "background-color": "#2f9e44", "background-opacity": 0.14, "border-color": "#2f9e44" } },
      { selector: "node:parent[state='checked']", style: { "background-color": "#f2b705", "background-opacity": 0.18, "border-color": "#c58a00" } },
      { selector: "node:parent[state='unchecked']", style: { "background-color": "#e8590c", "background-opacity": 0.14, "border-color": "#e8590c" } },
      { selector: "node:parent[state='empty']", style: { "background-color": "#c8c3bc", "background-opacity": 0.25, "border-color": "#9b958c" } },
      { selector: ".highlighted", style: { "border-color": "#1c7ed6", "border-width": 2 } },
      { selector: "edge.highlighted", style: { width: 2.4, "line-color": "#1c7ed6", "target-arrow-color": "#1c7ed6", opacity: 1 } }
    ],
    layout: {
      // Positions are computed at build time (module columns, dependency
      // depth stacking) — the generic JS layouts ignore compound
      // containment and scatter declarations away from their files.
      name: "preset", padding: 40, fit: true
    }
  });

  // Per-file force layout: spread each file's declarations inside the
  // cell the build pre-allocated for the cluster, with the file's own
  // dependency edges pulling neighbors closer. fCoSE's `randomize:
  // false` seeds the sim from the preset positions, so the page is
  // deterministic; the post-pass renormalizes every member into the
  // cell if the sim drifted out (fcose has no bounding-box constraint).
  // A failed/absent fcose CDN script degrades to the preset stacks.
  if (window.cytoscapeFcose) {
    var cells = {};
    payload.nodes.forEach(function (node) {
      if (node.group === "file" && node.cell) { cells[node.id] = node.cell; }
    });
    var clusterMembers = {};
    cy.nodes('[group = "declaration"]').forEach(function (decl) {
      (clusterMembers[decl.data("parent")] = clusterMembers[decl.data("parent")] || []).push(decl);
    });
    Object.keys(clusterMembers).forEach(function (fileId) {
      var cell = cells[fileId];
      var members = cy.collection(clusterMembers[fileId]);
      if (!cell || members.length < 2) { return; }
      var intra = members.connectedEdges('[kind = "depends"]').filter(function (edge) {
        return edge.source().data("parent") === fileId
          && edge.target().data("parent") === fileId;
      });
      members.union(intra).layout({
        name: "fcose", animate: false, randomize: false, fit: false,
        packComponents: false, quality: "default", numIter: 500,
        idealEdgeLength: 110, nodeRepulsion: 18000
      }).run();

      // Renormalize: translate/scale the cluster into its cell.
      var xs = members.map(function (m) { return m.position("x"); });
      var ys = members.map(function (m) { return m.position("y"); });
      var minX = Math.min.apply(null, xs); var maxX = Math.max.apply(null, xs);
      var minY = Math.min.apply(null, ys); var maxY = Math.max.apply(null, ys);
      var width = Math.max(maxX - minX, 1);
      var height = Math.max(maxY - minY, 1);
      var cellW = cell.x2 - cell.x1;
      var cellH = cell.y2 - cell.y1;
      var scale = Math.min(1, cellW / width, cellH / height);
      var cx = (minX + maxX) / 2;
      var cyCenter = (minY + maxY) / 2;
      var cellCx = (cell.x1 + cell.x2) / 2;
      var cellCy = (cell.y1 + cell.y2) / 2;
      members.forEach(function (m) {
        var p = m.position();
        m.position({
          x: cellCx + (p.x - cx) * scale,
          y: cellCy + (p.y - cyCenter) * scale
        });
      });
    });
  }

  cy.fit(undefined, 40);

  function moveTooltip(e) {
    var ev = e.originalEvent;
    if (!ev || typeof ev.clientX !== "number") { return; }
    tooltip.style.left = ev.clientX + 14 + "px";
    tooltip.style.top = ev.clientY + 14 + "px";
  }
  cy.on("mouseover", "node", function (e) {
    tooltip.innerHTML = e.target.data("tooltip") || "";
    tooltip.style.display = "block";
    moveTooltip(e);
  });
  cy.on("mousemove", "node", function (e) { moveTooltip(e); });
  cy.on("mouseout", "node", function () { tooltip.style.display = "none"; });

  var marked = [];
  function clearMark() {
    for (var i = 0; i < marked.length; i++) { marked[i].removeClass("highlighted"); }
    marked = [];
  }
  cy.on("tap", function (e) {
    if (e.target === cy) { clearMark(); return; }
    clearMark();
    marked = e.target.closedNeighborhood();
    for (var i = 0; i < marked.length; i++) { marked[i].addClass("highlighted"); }
  });
  cy.on("resize", function () { cy.fit(undefined, 40); });
})();
</script>
</body>
</html>
"""
