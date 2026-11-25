"""CLI-level tests for `axbt graph`, driven through the real entry point.

The suite stays offline: the Cytoscape.js CDN URL is asserted as text,
never fetched, and the embedded graph data is parsed straight out of
the generated page's JSON block.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import pytest
from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.graph import (
    _layout_positions,
    rendered_nodes,
    rollup_state,
    state_of,
    write_graph,
)
from axle_build_tool.manifest import (
    MANIFEST_VERSION,
    ExtractedDecl,
    Manifest,
    ManifestNode,
    load_manifest,
)
from axle_build_tool.manifest import manifest_path
from conftest import make_document

runner = CliRunner()

NO_TARGETS_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets: []
"""

# Same synthetic chain shapes tests/test_list.py proves out: a hoisted
# external import + module docstring (position shifts), an A <- B <- C
# chain, and a declaration-free file.
GRAPH_FILES = {
    "M/A.lean": (
        "import Mathlib\n\n/-! Base. -/\n\ndef base := 1\n"
        "theorem base_thm : base = 1 := rfl\n"
    ),
    "M/B.lean": "import A\ntheorem middle_thm : base = 1 := rfl\n",
    "M/C.lean": "import B\ntheorem gap : 1 = 2 := by sorry\n",
    "M/D.lean": "import Mathlib\n",
}

# One-based payload coordinates for each file's own extraction call:
# A's section starts at payload line 3 (hoisted import + blank), B's at
# 9, C's at 11. `middle_thm` carries a bare (`base`) and a bare-unique
# (`base_thm`) dependency, plus an unresolvable name whose edge must be
# skipped rather than guessed.
GRAPH_DOCS = {
    "def base := 1": {
        "base": make_document(
            "base", kind="def", line_pos=6, end_line_pos=6, signature="def base"
        ),
        "base_thm": make_document(
            "base_thm",
            kind="theorem",
            line_pos=7,
            end_line_pos=7,
            signature="theorem base_thm : base = 1 := rfl",
        ),
    },
    "theorem middle_thm": {
        "middle_thm": make_document(
            "middle_thm",
            kind="theorem",
            line_pos=9,
            end_line_pos=9,
            signature="theorem middle_thm : base = 1 := rfl",
            local_type_dependencies=["base"],
            local_syntactic_dependencies=["base_thm", "not_a_project_decl"],
        ),
    },
    "theorem gap": {
        "gap": make_document(
            "gap",
            kind="theorem",
            line_pos=11,
            end_line_pos=11,
            signature="theorem gap : 1 = 2 := by sorry",
            is_sorry=True,
        ),
    },
}


@pytest.fixture
def graph_project(tmp_path, make_project, fake_axle, monkeypatch) -> Path:
    """The chain project, compiled against the fake Axle client."""
    fake_axle._extract_documents_by_marker = GRAPH_DOCS
    root = make_project(tmp_path, NO_TARGETS_CONFIG, GRAPH_FILES)
    monkeypatch.chdir(root)
    result = runner.invoke(main, ["compile"])
    assert result.exit_code == 0, result.output
    return root


def graph_output_path(root: Path, args: tuple[str, ...]) -> Path:
    """The path `axbt graph` wrote to for these arguments."""
    for index, arg in enumerate(args):
        if arg in ("-o", "--output") and index + 1 < len(args):
            return root / args[index + 1]
    return root / ".axbt" / "graph.html"


def run_graph(root: Path, *args: str) -> tuple[str, str]:
    """Run `axbt graph` and return (CLI output, rendered HTML)."""
    result = runner.invoke(main, ["graph", *args])
    assert result.exit_code == 0, result.output
    html_text = graph_output_path(root, args).read_text(encoding="utf-8")
    return result.output, html_text


def graph_data(html_text: str) -> dict:
    """The embedded JSON payload, parsed the way the page parses it."""
    match = re.search(
        r'<script type="application/json" id="graph-data">(.*?)</script>',
        html_text,
        re.DOTALL,
    )
    assert match, '<script type="application/json" id="graph-data"> missing'
    blob = match.group(1)
    # The embedding must contain no raw angle brackets at all: not even
    # the legitimate breakout candidate `</script>` can be formed.
    assert "<" not in blob and ">" not in blob
    return json.loads(blob)


def by_id(data: dict, element_id: str) -> dict:
    (element,) = [element for element in data["nodes"] if element["id"] == element_id]
    return element


def apply_stamps(root: Path, stamps: dict[str, str]) -> None:
    """Stamp declarations in the persisted manifest (`checked`/`verified`)."""
    manifest = load_manifest(root)
    nodes = []
    for node in manifest.nodes:
        declarations = []
        for decl in node.declarations:
            if decl.name in stamps:
                now = datetime(2026, 1, 1, tzinfo=timezone.utc)
                update = {"checked_sig": "c" * 32, "checked_at": now}
                if stamps[decl.name] == "verified":
                    update.update(
                        verified_sig="v" * 32,
                        verified_at=now,
                        verified_request_id="req-v",
                    )
                decl = decl.model_copy(update=update)
            declarations.append(decl)
        nodes.append(node.model_copy(update={"declarations": declarations}))
    from axle_build_tool.manifest import save_manifest

    save_manifest(manifest.model_copy(update={"nodes": nodes}), root)


class TestGraphRender:
    def test_default_output_counts_and_offline_render(
        self, graph_project: Path, fake_axle
    ) -> None:
        fake_axle.calls.clear()

        output, html_text = run_graph(graph_project)

        # Rendering is fully offline: nothing was submitted.
        assert fake_axle.calls == []
        rendered = graph_project / ".axbt" / "graph.html"
        assert rendered.is_file()
        assert "Wrote graph to" in output
        assert str(rendered) in output
        # 4 files (D is declaration-free), 4 declarations; the edges:
        # two import edges + `base`/`base_thm` into `middle_thm`.
        assert re.search(
            r"\(1 module\(s\), 4 file\(s\), 4 declaration\(s\), 4 edge\(s\)\)",
            output,
        )
        data = graph_data(html_text)
        assert data["counts"] == {
            "modules": 1,
            "files": 4,
            "declarations": 4,
            "edges": 4,
        }

    def test_page_carries_the_pinned_cdn_script_and_compound_shape(
        self, graph_project: Path
    ) -> None:
        output, html_text = run_graph(graph_project)

        # The single external reference: the pinned, SRI-hashed Cytoscape CDN script.
        assert (
            "https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.31.0/cytoscape.min.js"
            in html_text
        )
        assert "cytoscape-fcose" not in html_text
        assert "layout-base" not in html_text
        assert "cose-base" not in html_text
        assert 'integrity="' in html_text and 'crossorigin="anonymous"' in html_text
        # No other network references anywhere in the page.
        urls = re.findall(r"https?://[^\s\"']+", html_text)
        assert all(url.startswith("https://cdnjs.cloudflare.com") for url in urls)

        data = graph_data(html_text)
        ids = [node["id"] for node in data["nodes"]]
        # Compound hierarchy: the module compound precedes its files,
        # which precede their declarations.
        assert ids[0] == "module:M"
        assert {"file:M.A", "file:M.B", "file:M.C", "file:M.D"} <= set(ids)
        assert {
            "decl:M.A:base",
            "decl:M.A:base_thm",
            "decl:M.B:middle_thm",
            "decl:M.C:gap",
        } <= set(ids)
        for node in data["nodes"]:
            if node["group"] == "declaration":
                assert node["parent"].startswith("file:")
            elif node["group"] == "file":
                assert node["parent"].startswith("module:")
            else:
                assert node["parent"] is None

    def test_file_selection_renders_the_closure_subgraph(
        self, graph_project: Path
    ) -> None:
        output, html_text = run_graph(graph_project, "--select", "M.B")

        data = graph_data(html_text)
        ids = {node["id"] for node in data["nodes"]}
        # B plus its dependency closure; C and D (with their files'
        # members) are out of the picture entirely.
        assert {"module:M", "file:M.A", "file:M.B"} == {
            item for item in ids if not item.startswith("decl:")
        }
        assert {item for item in ids if item.startswith("decl:")} == {
            "decl:M.A:base",
            "decl:M.A:base_thm",
            "decl:M.B:middle_thm",
        }
        assert data["counts"]["files"] == 2

    def test_declaration_selection_brings_owning_file_and_ancestors(
        self, graph_project: Path
    ) -> None:
        output, html_text = run_graph(graph_project, "--select", "M.C.gap")

        data = graph_data(html_text)
        file_ids = {n["id"] for n in data["nodes"] if n["group"] == "file"}
        assert file_ids == {"file:M.A", "file:M.B", "file:M.C"}
        # The owning file renders *all* of its declarations, not just
        # the selected one.
        assert "decl:M.C:gap" in {n["id"] for n in data["nodes"]}

    def test_custom_output_path(self, graph_project: Path) -> None:
        output, html_text = run_graph(graph_project, "--output", "custom.html")

        assert "Wrote graph to" in output
        assert (graph_project / "custom.html").is_file()
        # The default path was not written to.
        assert not (graph_project / ".axbt" / "graph.html").exists()

    def test_decl_edge_toggle_is_wired_in_page(self, graph_project: Path) -> None:
        output, html_text = run_graph(graph_project)

        # The legend carries the checkbox UNTICKED (the arrows overload
        # the picture by default), the CSS knows the hidden treatment,
        # and the script looks the id up and applies the state once.
        assert 'id="toggle-decl-edges"' in html_text
        assert "declaration dependency arrows" in html_text
        assert 'type="checkbox" id="toggle-decl-edges" checked' not in html_text
        assert "edge.hidden" in html_text
        assert html_text.count("toggle-decl-edges") >= 2
        # The tap handler runs the reveal-or-restore rule through the
        # same visibility function the checkbox drives.
        assert "refreshEdgeVisibility" in html_text

    def test_defs_and_theorems_render_different_shapes(
        self, graph_project: Path
    ) -> None:
        """Verify-verifiable kinds (theorem/lemma/example) are circles;
        never-verifiable declarations (defs, instances, ...) are
        rounded squares — a color-independent distinction the legend
        spells out."""
        output, html_text = run_graph(graph_project)

        data = graph_data(html_text)
        kinds = {
            node["id"]: node["kind"]
            for node in data["nodes"]
            if node["group"] == "declaration"
        }
        assert kinds["decl:M.A:base"] == "def"
        assert kinds["decl:M.A:base_thm"] == "theorem"
        # The legend explains the shape split.
        assert "verifiable" in html_text
        assert "never verifiable" in html_text
        # The style sheet drives the split: solid rectangles by default
        # for defs/structures, ellipses for the proof kinds via kind selectors.
        assert 'shape: "rectangle" } }' in html_text
        assert 'shape: "ellipse" } }' in html_text
        assert "node[kind='theorem'], node[kind='lemma'], node[kind='example']" in html_text

    def test_dragging_is_enabled_with_a_reset_control(
        self, graph_project: Path
    ) -> None:
        output, html_text = run_graph(graph_project)

        # Nodes and compounds must be grabbable: the explicit
        # autoungrabify flag is gone, and a reset button restores the
        # deterministic spread after rearranging.
        assert "autoungrabify" not in html_text
        assert 'id="reset-positions"' in html_text
        assert "reset layout" in html_text
        assert html_text.count("reset-positions") >= 2
        assert "spreadFileClusters()" in html_text

    def test_missing_manifest_fails_with_compile_hint(
        self, make_project, tmp_path: Path, monkeypatch
    ) -> None:
        root = make_project(tmp_path, NO_TARGETS_CONFIG, GRAPH_FILES)
        monkeypatch.chdir(root)

        result = runner.invoke(main, ["graph"])

        assert result.exit_code != 0
        assert "compile" in result.output

    def test_stale_manifest_fails_with_compile_hint(
        self, graph_project: Path
    ) -> None:
        raw = json.loads(manifest_path(graph_project).read_text(encoding="utf-8"))
        raw["version"] = MANIFEST_VERSION + 1
        manifest_path(graph_project).write_text(json.dumps(raw, indent=2), encoding="utf-8")

        result = runner.invoke(main, ["graph"])

        assert result.exit_code != 0
        assert "compile" in result.output

    def test_unknown_selection_module_fails_with_guidance(
        self, graph_project: Path
    ) -> None:
        result = runner.invoke(main, ["graph", "--select", "Nope"])

        assert result.exit_code != 0
        assert "Unknown module 'Nope'" in result.output

    def test_tooltips_carry_file_and_declaration_metadata(
        self, graph_project: Path
    ) -> None:
        output, html_text = run_graph(graph_project)

        module_manifest = load_manifest(graph_project)
        file_b = module_manifest.by_name()["M.B"]
        rendered_b = by_id(graph_data(html_text), "file:M.B")
        assert file_b.path in rendered_b["tooltip"]
        assert file_b.md5 in rendered_b["tooltip"]
        assert ("new ✱" if file_b.status == "new" else file_b.status) in rendered_b["tooltip"]

        middle = by_id(graph_data(html_text), "decl:M.B:middle_thm")
        assert "theorem" in middle["tooltip"]
        assert "middle_thm" in middle["tooltip"]
        assert file_b.path in middle["tooltip"]
        assert "—" in middle["tooltip"]  # no stamps recorded yet

    def test_manifest_names_are_never_interpolated_raw(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A hostile declaration name cannot inject markup: extraction
        names are JSON-escaped (no raw `<` can appear) and the tooltip
        markup double-escapes them to entities."""
        root = make_project(tmp_path, NO_TARGETS_CONFIG, {"M/A.lean": "def x := 1\n"})
        monkeypatch.chdir(root)
        fake_axle._extract_documents_by_marker = {
            "def x := 1": {
                "evil</script><img>": make_document(
                    "evil</script><img>",
                    kind="def",
                    line_pos=1,
                    end_line_pos=1,
                    signature="def x",
                ),
            },
        }
        compile_result = runner.invoke(main, ["compile"])
        assert compile_result.exit_code == 0, compile_result.output

        output, html_text = run_graph(root)

        # Exactly four script elements: Cytoscape CDN, KaTeX CDN, the JSON
        # data block, and the application script.
        assert html_text.count("</script>") == 4
        data = graph_data(html_text)
        (declaration,) = [n for n in data["nodes"] if n["group"] == "declaration"]
        assert declaration["id"].endswith("evil</script><img>")
        assert "&lt;/script&gt;&lt;img&gt;" in declaration["tooltip"]

    def test_changed_files_carry_the_red_asterisk_marker(
        self, graph_project: Path, fake_axle
    ) -> None:
        # First compile: everything is `new` — every file starred.
        output, html_text = run_graph(graph_project)
        data = graph_data(html_text)
        assert all(node["changed"] for node in data["nodes"] if node["group"] == "file")
        assert all("✱" in node["label"] for node in data["nodes"] if node["group"] == "file")

        # A clean re-compile: not a star anywhere...
        assert runner.invoke(main, ["compile"]).exit_code == 0
        output, html_text = run_graph(graph_project)
        data = graph_data(html_text)
        assert not any(node["changed"] for node in data["nodes"])
        labels = [node["label"] for node in data["nodes"]]
        assert not any("✱" in label for label in labels)

        # ...until a file's source changes: exactly B is starred again.
        (graph_project / "M/B.lean").write_text(
            "import A\ntheorem middle_thm : base = 1 := rfl\n-- touched\n",
            encoding="utf-8",
        )
        fake_axle._extract_documents_by_marker = {
            **GRAPH_DOCS,
            "-- touched": {
                "middle_thm": make_document(
                    "middle_thm",
                    kind="theorem",
                    line_pos=9,
                    end_line_pos=9,
                    signature="theorem middle_thm : base = 1 := rfl",
                    local_type_dependencies=["base"],
                    local_syntactic_dependencies=["base_thm", "not_a_project_decl"],
                ),
            },
        }
        assert runner.invoke(main, ["compile"]).exit_code == 0

        output, html_text = run_graph(graph_project)
        data = graph_data(html_text)
        assert [n["id"] for n in data["nodes"] if n["changed"]] == [
            "file:M.B",
            "decl:M.B:middle_thm",
        ]


class TestGraphColors:
    """Colors key only on the outcome stamps — never inferred."""

    def test_stamp_states_and_container_rollup(self, graph_project: Path) -> None:
        apply_stamps(
            graph_project,
            {"base": "checked", "base_thm": "checked", "gap": "verified"},
        )

        output, html_text = run_graph(graph_project)

        # A checked def is DONE (green): `verify` can never judge it, so
        # a clean check is its terminal tier — yellow is reserved for
        # kernally-verification-pending kinds.
        assert by_id(data := graph_data(html_text), "decl:M.A:base")["state"] == "done"
        assert by_id(data, "decl:M.A:base_thm")["state"] == "checked"
        assert by_id(data, "decl:M.B:middle_thm")["state"] == "unchecked"
        # A verified theorem is green as always.
        assert by_id(data, "decl:M.C:gap")["state"] == "verified"
        # Container rollup: the weakest constituent color. A's mix is
        # checked (a kernel-pending theorem), B is unchecked, and the
        # declaration-free D is empty.
        assert by_id(data, "file:M.A")["state"] == "checked"
        assert by_id(data, "file:M.B")["state"] == "unchecked"
        assert by_id(data, "file:M.D")["state"] == "empty"
        assert by_id(data, "module:M")["state"] == "unchecked"

    def test_kernel_pending_theorem_keeps_its_file_yellow(
        self, graph_project: Path
    ) -> None:
        """A checked def reads done (green), but its file still carries
        an unchecked theorem — the container honestly reads the weakest
        member state, not the def's green."""
        apply_stamps(graph_project, {"base": "checked"})

        output, html_text = run_graph(graph_project)

        data = graph_data(html_text)
        assert by_id(data, "decl:M.A:base")["state"] == "done"
        assert by_id(data, "decl:M.A:base_thm")["state"] == "unchecked"
        assert by_id(data, "file:M.A")["state"] == "unchecked"

    def test_verified_stamps_on_defs_stay_green(
        self, graph_project: Path
    ) -> None:
        """A verified stamp on a def is practically impossible (verify
        refuses defs), but if a manifest carries one, green is still the
        honest rendering, keyed only on the stamps."""
        apply_stamps(graph_project, {"base": "verified"})

        output, html_text = run_graph(graph_project)

        assert by_id(graph_data(html_text), "decl:M.A:base")["state"] == "verified"

    def test_stamps_are_surfaced_in_the_tooltip(self, graph_project: Path) -> None:
        apply_stamps(graph_project, {"base": "verified"})

        output, html_text = run_graph(graph_project)

        base = by_id(graph_data(html_text), "decl:M.A:base")
        assert "2026-01-01" in base["tooltip"]
        middle = by_id(graph_data(html_text), "decl:M.B:middle_thm")
        assert "—" in middle["tooltip"]

    def test_unstamped_manifests_degrade_to_the_untiered_palette(
        self, graph_project: Path
    ) -> None:
        """Manifests written before the check-stamp contract carry no
        stamps: every declaration renders orange ('no recorded check')
        and nothing is inferred as 'checked'."""
        output, html_text = run_graph(graph_project)

        decls = [n for n in graph_data(html_text)["nodes"] if n["group"] == "declaration"]
        assert all(node["state"] == "unchecked" for node in decls)
        assert by_id(graph_data(html_text), "module:M")["state"] == "unchecked"

    def test_legend_is_rendered_in_page(self, graph_project: Path) -> None:
        output, html_text = run_graph(graph_project)

        assert 'id="legend-panel"' not in html_text
        assert "color = outcome stamps only" not in html_text
        drawer_top = html_text.split('<div class="drawer-top">', 1)[1].split(
            '<div class="drawer-body"', 1
        )[0]
        assert 'id="search-nodes"' in drawer_top
        assert 'id="toggle-decl-edges"' in drawer_top
        assert 'id="toggle-transitive-edges"' in drawer_top
        assert 'id="reset-positions"' in drawer_top

    def test_state_of_keys_only_on_stamps(self, graph_project: Path) -> None:
        bare_theorem = ExtractedDecl(
            name="d", kind="theorem", is_sorry=False, line_pos=1, end_line_pos=1
        )
        assert state_of(bare_theorem) == "unchecked"
        checked = bare_theorem.model_copy(
            update={"checked_sig": "c", "checked_at": datetime(2026, 1, 1, tzinfo=timezone.utc)}
        )
        assert state_of(checked) == "checked"
        verified = checked.model_copy(
            update={"verified_sig": "v", "verified_at": datetime(2026, 1, 1, tzinfo=timezone.utc)}
        )
        assert state_of(verified) == "verified"

        # The never-verifiable sibling kinds: checked reads `done`, not
        # the kernel-verification-pending yellow.
        bare_def = bare_theorem.model_copy(update={"kind": "def"})
        assert state_of(bare_def) == "unchecked"
        assert state_of(bare_def.model_copy(update={"checked_sig": "c", "checked_at": checked.checked_at})) == "done"

    def test_defs_in_verified_file_or_verified_closure_render_done_green(
        self, graph_project: Path
    ) -> None:
        """When `axbt verify` verifies a theorem without a separate
        `axbt check` run, `verified_sig` is stamped only on theorems even
        though Lean's kernel checked the definitions in the file/closure.
        Those definitions render as `done` (green) rather than `unchecked`."""
        manifest = load_manifest(graph_project)
        now = datetime(2026, 1, 1, tzinfo=timezone.utc)
        nodes = []
        for node in manifest.nodes:
            decls = []
            for d in node.declarations:
                if d.name == "base_thm":
                    d = d.model_copy(
                        update={"verified_sig": "v" * 32, "verified_at": now}
                    )
                decls.append(d)
            nodes.append(node.model_copy(update={"declarations": decls}))
        from axle_build_tool.manifest import save_manifest

        save_manifest(manifest.model_copy(update={"nodes": nodes}), graph_project)

        _output, html_text = run_graph(graph_project)
        data = graph_data(html_text)
        assert by_id(data, "decl:M.A:base")["state"] == "done"
        assert by_id(data, "decl:M.A:base_thm")["state"] == "verified"
        assert by_id(data, "file:M.A")["state"] == "verified"


class TestGraphEdges:
    def test_import_and_dependency_edges_are_directed(self, graph_project: Path) -> None:
        output, html_text = run_graph(graph_project)

        edges = {edge["id"]: edge for edge in graph_data(html_text)["edges"]}
        # File import edges point dependency -> dependent.
        assert edges["import:M.A->M.B"]["source"] == "file:M.A"
        assert edges["import:M.A->M.B"]["target"] == "file:M.B"
        assert edges["import:M.B->M.C"]["kind"] == "import"
        # Declaration edges point dependency -> dependent as well.
        assert edges["dep:decl:M.A:base->decl:M.B:middle_thm"]["kind"] == "depends"
        assert edges["dep:decl:M.A:base_thm->decl:M.B:middle_thm"]["kind"] == "depends"

    def test_unresolvable_dependency_names_are_skipped(self, graph_project: Path) -> None:
        """`not_a_project_decl` names nothing in the rendered set: no
        edge is invented for it."""
        output, html_text = run_graph(graph_project)

        depended = [e for e in graph_data(html_text)["edges"] if e["kind"] == "depends"]
        assert len(depended) == 2
        assert all("not_a_project_decl" not in edge["id"] for edge in depended)

    def test_transitive_import_edges_are_flagged_and_toggled(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = make_project(
            tmp_path,
            NO_TARGETS_CONFIG,
            {
                "M/A.lean": "def a := 1\n",
                "M/B.lean": "import A\ndef b := a\n",
                "M/C.lean": "import A\nimport B\ndef c := b\n",
            },
        )
        fake_axle._extract_documents_by_marker = {
            "def a := 1": {"a": make_document("a", kind="def", line_pos=1, end_line_pos=1)},
            "def b := a": {"b": make_document("b", kind="def", line_pos=3, end_line_pos=3)},
            "def c := b": {"c": make_document("c", kind="def", line_pos=5, end_line_pos=5)},
        }
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        _output, html_text = run_graph(root)
        edges = {edge["id"]: edge for edge in graph_data(html_text)["edges"]}
        assert edges["import:M.A->M.B"]["transitive"] is False
        assert edges["import:M.B->M.C"]["transitive"] is False
        assert edges["import:M.A->M.C"]["transitive"] is True
        assert 'id="toggle-transitive-edges"' in html_text
        assert 'id="search-nodes"' in html_text
        assert 'id="inspector"' in html_text

    def test_upstream_and_downstream_highlighting_are_distinct(
        self, graph_project: Path
    ) -> None:
        """Selecting a node highlights upstream dependencies in light blue
        and downstream dependents in light pink across the graph, legend,
        and inspector."""
        _output, html_text = run_graph(graph_project)

        # Cytoscape stylesheet styles upstream (light blue) vs downstream
        # (light pink) separately for both nodes and edges, with a white
        # border on the selected focal node.
        assert '{ selector: "node.upstream", style: { "border-color": "#7dd3fc"' in html_text
        assert '{ selector: "edge.upstream", style: { width: 2.5, "line-color": "#7dd3fc"' in html_text
        assert '{ selector: "node.downstream", style: { "border-color": "#f9a8d4"' in html_text
        assert '{ selector: "edge.downstream", style: { width: 2.5, "line-color": "#f9a8d4"' in html_text
        assert '{ selector: ".selected-node", style: { "border-color": "#f8fafc"' in html_text

        # Cone traversal and selection apply directional classes.
        assert "return { upstream: upstream, downstream: downstream, all: all };" in html_text
        assert 'addClass("highlighted upstream")' in html_text
        assert 'addClass("highlighted downstream")' in html_text
        assert 'addClass("highlighted selected-node")' in html_text

        # Inspector matches the upstream/downstream color coding.
        assert "sg-pill upstream" in html_text
        assert "sg-pill downstream" in html_text
        assert "insp-sec upstream" in html_text
        assert "insp-sec downstream" in html_text
        assert "insp-chip upstream" in html_text
        assert "insp-chip downstream" in html_text


class TestRollup:
    """The container rollup rule (weakest constituent state wins)."""

    def test_weakest_constituent_state_wins(self) -> None:
        assert rollup_state(["verified"]) == "verified"
        assert rollup_state(["verified", "done"]) == "verified"
        assert rollup_state(["verified", "checked"]) == "checked"
        assert rollup_state(["done", "checked"]) == "checked"
        assert rollup_state(["verified", "checked", "unchecked"]) == "unchecked"

    def test_declaration_free_containers_are_empty(self) -> None:
        assert rollup_state([]) == "empty"

    def test_def_only_containers_roll_up_naturally(self) -> None:
        """A def-only file checked clean: all members are `done`, and
        the container reads green — its terminal on that tier."""
        assert rollup_state(["done", "done"]) == "done"
        # A kernel-pending theorem keeps the container yellow.
        assert rollup_state(["done", "checked"]) == "checked"


class TestLayout:
    """The build-time module-column layout (no JS layout at all)."""

    @staticmethod
    def node(name: str, parents: tuple[str, ...], declarations: list[str] = ()) -> ManifestNode:
        return ManifestNode(
            name=name,
            module=name.split(".", 1)[0],
            path=f"{name.replace('.', '/')}.lean",
            md5="0" * 32,
            status="clean",
            parents=list(parents),
            declarations=[
                ExtractedDecl(
                    name=decl,
                    kind="theorem",
                    is_sorry=False,
                    line_pos=index + 1,
                    end_line_pos=index + 1,
                )
                for index, decl in enumerate(declarations, start=1)
            ],
        )

    def test_modules_order_left_to_right_by_dependency_depth(self) -> None:
        files = [
            self.node("Core.CoreFile", (), ["one"]),
            self.node("App.AppFile", ("Core.CoreFile",), ["two"]),
            self.node("Zoom.ZoomFile", ("Core.CoreFile",), ["three"]),
        ]
        positions, _cells = _layout_positions(files)
        core_x = positions["file:Core.CoreFile"]["x"]
        app_x = positions["file:App.AppFile"]["x"]
        zoom_x = positions["file:Zoom.ZoomFile"]["x"]
        # The dependency-importing modules sit right of their dependency.
        assert core_x < app_x and core_x < zoom_x
        assert [app_x, zoom_x] == sorted([app_x, zoom_x])

    def test_declarations_stack_by_intra_file_dep_depth_then_source_line(self) -> None:
        # Independent declarations keep their source line order (beta at
        # line 2 precedes alpha at line 3).
        files = [self.node("Core.CoreFile", (), ["beta", "alpha"])]
        positions, _cells = _layout_positions(files)
        alpha, beta = positions["decl:Core.CoreFile:alpha"], positions["decl:Core.CoreFile:beta"]
        assert beta["y"] < alpha["y"]
        assert alpha["x"] == beta["x"]

        # When an earlier-line declaration depends on a later-line
        # declaration in the same file, intra-file dependency depth places
        # the dependency first.
        with_intra_dep = ManifestNode(
            name="Core.DepFile",
            module="Core",
            path="Core/DepFile.lean",
            md5="0" * 32,
            status="clean",
            parents=[],
            declarations=[
                ExtractedDecl(
                    name="derived",
                    kind="theorem",
                    is_sorry=False,
                    line_pos=2,
                    end_line_pos=2,
                    dependencies=["helper"],
                ),
                ExtractedDecl(
                    name="helper",
                    kind="lemma",
                    is_sorry=False,
                    line_pos=5,
                    end_line_pos=5,
                    dependencies=[],
                ),
            ],
        )
        pos2, _ = _layout_positions([with_intra_dep])
        assert pos2["decl:Core.DepFile:helper"]["y"] < pos2["decl:Core.DepFile:derived"]["y"]

    def test_cluster_stacking_places_dependent_files_right_and_siblings_below(
        self,
    ) -> None:
        # Dependent files within a module advance left-to-right across
        # rank columns; same-rank sibling files stack top-to-bottom.
        files = [
            self.node("Core.CoreFile", ()),
            self.node("Core.Sibling", ()),
            self.node("Core.Empty", ("Core.CoreFile",)),
        ]
        positions, _cells = _layout_positions(files)
        assert positions["file:Core.Sibling"]["x"] == positions["file:Core.CoreFile"]["x"]
        assert positions["file:Core.Sibling"]["y"] > positions["file:Core.CoreFile"]["y"]
        assert positions["file:Core.Empty"]["x"] > positions["file:Core.CoreFile"]["x"]

    def test_large_file_wraps_into_non_overlapping_pill_subcolumns(self) -> None:
        from axle_build_tool.graph import _PILL_H, _pill_width

        decls = [f"theorem_name_{i:02d}_long" for i in range(60)]
        node = self.node("Core.Big", (), decls)
        positions, cells = _layout_positions([node])
        cell = cells["file:Core.Big"]

        boxes = []
        for d in decls:
            pos = positions[f"decl:Core.Big:{d}"]
            w = _pill_width(d)
            boxes.append((pos["x"] - w / 2, pos["y"] - _PILL_H / 2, pos["x"] + w / 2, pos["y"] + _PILL_H / 2))
            assert cell["x1"] <= pos["x"] - w / 2 and pos["x"] + w / 2 <= cell["x2"]
            assert cell["y1"] <= pos["y"] - _PILL_H / 2 and pos["y"] + _PILL_H / 2 <= cell["y2"]

        # Multiple sub-columns used (4 sub-columns for 60 declarations)
        assert len({positions[f"decl:Core.Big:{d}"]["x"] for d in decls}) == 4
        # Zero pairwise pill bounding-box overlap
        for i in range(len(boxes)):
            x1a, y1a, x2a, y2a = boxes[i]
            for j in range(i + 1, len(boxes)):
                x1b, y1b, x2b, y2b = boxes[j]
                separated = x2a < x1b or x2b < x1a or y2a < y1b or y2b < y1a
                assert separated, f"pill {i} and pill {j} overlap"

    def test_positions_cover_every_element(self) -> None:
        files = [
            self.node("Core.CoreFile", ()),
            self.node("Core.Empty", ("Core.CoreFile",)),
        ]
        positions, _cells = _layout_positions(files)
        assert set(positions) == {
            "file:Core.CoreFile",
            "file:Core.Empty",
            "module:Core",
        }
        for position in positions.values():
            assert isinstance(position["x"], int)
            assert isinstance(position["y"], int)

    def test_repeated_renders_are_byte_identical(self, graph_project: Path) -> None:
        output, first = run_graph(graph_project)
        output, second = run_graph(graph_project)
        assert first == second

    def test_positions_are_embedded_for_preset_layout(
        self, graph_project: Path
    ) -> None:
        output, html_text = run_graph(graph_project)

        data = graph_data(html_text)
        for node in data["nodes"]:
            assert isinstance(node["position"]["x"], int)
            assert isinstance(node["position"]["y"], int)
        # No JS-graph-layout markers left: positions come from the data.
        assert "preset" in html_text
        assert "breadthfirst" not in html_text

    def test_cross_module_import_cycle_renders_cleanly(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """File-acyclic cross-module zig-zag imports induce a cycle between
        modules; `axbt graph` must render without RecursionError."""
        root = make_project(
            tmp_path,
            "modules:\n  ModA:\n    targets: []\n  ModB:\n    targets: []\n",
            {
                "ModA/Base.lean": "def a1 := 1\n",
                "ModB/Mid.lean": "import Base\ndef b1 := a1\n",
                "ModA/Top.lean": "import Mid\ndef a2 := b1\n",
            },
        )
        fake_axle._extract_documents_by_marker = {
            "def a1 := 1": {
                "a1": make_document("a1", kind="def", line_pos=1, end_line_pos=1)
            },
            "def b1 := a1": {
                "b1": make_document("b1", kind="def", line_pos=3, end_line_pos=3)
            },
            "def a2 := b1": {
                "a2": make_document("a2", kind="def", line_pos=5, end_line_pos=5)
            },
        }
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        _output, html_text = run_graph(root)
        data = graph_data(html_text)
        assert data["counts"]["modules"] == 2
        assert data["counts"]["files"] == 3

    def test_cross_module_cycle_layout_is_deterministic_across_hash_seeds(
        self,
    ) -> None:
        snippet = (
            "from axle_build_tool.manifest import ManifestNode\n"
            "from axle_build_tool.graph import _layout_positions\n"
            "def mk(name, parents):\n"
            "    return ManifestNode(name=name, module=name.split('.', 1)[0], "
            "path=f'{name}.lean', md5='0'*32, status='clean', parents=list(parents))\n"
            "files = [\n"
            "    mk('App.Main', ['CoreA.F1', 'CoreB.F1']),\n"
            "    mk('CoreA.F1', ['CoreB.F2']),\n"
            "    mk('CoreA.F2', []),\n"
            "    mk('CoreB.F1', ['CoreA.F2']),\n"
            "    mk('CoreB.F2', ['CoreA.F2']),\n"
            "]\n"
            "pos, _ = _layout_positions(files)\n"
            "print(sorted((k, pos[k]['x'], pos[k]['y']) for k in pos))\n"
        )
        results = {
            subprocess.check_output(
                [sys.executable, "-c", snippet],
                env={**os.environ, "PYTHONHASHSEED": str(seed)},
                text=True,
            ).strip()
            for seed in range(6)
        }
        assert len(results) == 1

    def test_dense_transitive_dag_layout_completes_quickly(self) -> None:
        files = [
            self.node(
                f"M.F{i:02d}",
                tuple(f"M.F{j:02d}" for j in range(i)),
            )
            for i in range(30)
        ]
        started = time.monotonic()
        positions, _cells = _layout_positions(files)
        elapsed = time.monotonic() - started
        assert elapsed < 1.0
        coords = [
            (positions[f"file:M.F{i:02d}"]["x"], positions[f"file:M.F{i:02d}"]["y"])
            for i in range(30)
        ]
        assert coords == sorted(coords)
        assert len(set(coords)) == 30

    def test_deep_chain_exceeding_recursion_limit_does_not_overflow(self) -> None:
        depth = sys.getrecursionlimit() + 200
        nodes = [
            self.node(f"M.F{i:04d}", (f"M.F{i - 1:04d}",) if i > 0 else ())
            for i in range(depth)
        ]
        manifest = Manifest(
            generated_at=datetime.now(timezone.utc),
            nodes=nodes,
        )
        closure = rendered_nodes(manifest, [nodes[-1]])
        assert len(closure) == depth

        positions, _cells = _layout_positions(closure)
        coords = [
            (positions[f"file:M.F{i:04d}"]["x"], positions[f"file:M.F{i:04d}"]["y"])
            for i in range(depth)
        ]
        assert coords == sorted(coords)
        assert len(set(coords)) == depth

    def test_cyclic_manifest_terminates_cleanly(self) -> None:
        nodes = [
            self.node("M.A", ("M.B",)),
            self.node("M.B", ("M.A",)),
        ]
        manifest = Manifest(
            generated_at=datetime.now(timezone.utc),
            nodes=nodes,
        )
        closure = rendered_nodes(manifest, [nodes[0]])
        assert [node.name for node in closure] == ["M.A", "M.B"]

        positions, _cells = _layout_positions(closure)
        assert set(positions) == {"file:M.A", "file:M.B", "module:M"}

    def test_write_graph_builds_graph_data_once(
        self, graph_project: Path, monkeypatch
    ) -> None:
        import axle_build_tool.graph as graph_mod

        calls = 0
        original = graph_mod.build_graph_data

        def counted(manifest, files):
            nonlocal calls
            calls += 1
            return original(manifest, files)

        monkeypatch.setattr(graph_mod, "build_graph_data", counted)
        manifest = load_manifest(graph_project)
        write_graph(manifest, graph_project, manifest.nodes)
        assert calls == 1


class TestSearchInspectorAndDocs:
    """Comprehensive search auto-complete, dockable inspector, source viewer,
    and Markdown + LaTeX docstring rendering."""

    def test_markdown_and_latex_renderer_handles_math_and_escapes_html(self) -> None:
        from axle_build_tool.graph import render_markdown_latex

        md = (
            "# Prime bound\n\n"
            "For any $\\alpha \\in \\mathbb{N}$ with $\\alpha \\le n$, we have\n"
            "$a \\bmod m = b \\pmod{p}$, $P \\longleftrightarrow Q \\Longleftrightarrow R$,\n"
            "and $\\texttt{SqrtRemSpec}(N, s, r)$ via \\texttt{spec_sqrt_eq}:\n\n"
            "$$\\texttt{SqrtRemSpec}\\left(N,\\ \\texttt{Nat.sqrt} N,\\ N - (\\texttt{Nat.sqrt} N)^2\\right)$$\n\n"
            "$$\\frac{\\sqrt{x^2 + 1}}{2} \\to \\infty$$\n\n"
            "\\begin{aligned}\n"
            "a &\\equiv b \\pmod{m} \\\\\n"
            "c &= d\n"
            "\\end{aligned}\n\n"
            "Uses **helper** (`prime_dvd_square`) and *descent*.\n"
            "Also escapes <script>alert(1)</script> and [bad](javascript:alert(1)).\n\n"
            "```lean\ntheorem demo : 1 = 1 := rfl\n```"
        )
        rendered = render_markdown_latex(md)
        assert "<h1>Prime bound</h1>" in rendered
        assert '<span class="math-inline" data-latex="\\alpha \\in \\mathbb{N}">' in rendered
        assert '<span class="math-inline" data-latex="\\alpha \\le n">' in rendered
        assert '<span class="math-inline" data-latex="a \\bmod m = b \\pmod{p}">' in rendered
        assert '<span class="math-inline" data-latex="P \\longleftrightarrow Q \\Longleftrightarrow R">' in rendered
        assert '<span class="math-inline" data-latex="\\texttt{SqrtRemSpec}(N, s, r)">' in rendered
        assert (
            '<div class="math-display" data-latex="\\texttt{SqrtRemSpec}\\left(N,\\ \\texttt{Nat.sqrt} N,\\ N - (\\texttt{Nat.sqrt} N)^2\\right)">'
            in rendered
        )
        assert '<div class="math-display" data-latex="\\frac{\\sqrt{x^2 + 1}}{2} \\to \\infty">' in rendered
        assert '<div class="math-display" data-latex="\\begin{aligned}\na &amp;\\equiv b \\pmod{m} \\\\\nc &amp;= d\n\\end{aligned}">' in rendered
        assert '<code class="md-inline-code">spec_sqrt_eq</code>' in rendered
        assert "<strong>helper</strong>" in rendered
        assert '<code class="md-inline-code">prime_dvd_square</code>' in rendered
        assert "<em>descent</em>" in rendered
        assert '<pre class="md-code"><code>' in rendered
        assert '<span class="hljs-keyword">theorem</span>' in rendered
        assert '<span class="hljs-title">demo</span>' in rendered
        assert '<span class="hljs-keyword">rfl</span>' in rendered
        # Raw HTML and unsafe URI schemes are neutralized.
        assert "<script>" not in rendered
        assert "&lt;script&gt;alert(1)&lt;/script&gt;" in rendered
        assert "javascript:" not in rendered

    def test_docs_code_and_search_autocomplete_ui_are_embedded(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        from axle_build_tool.graph import KATEX_CSS_URL, KATEX_JS_URL

        files = {
            "M/Base.lean": (
                "import Mathlib\n\n"
                "/-!\n"
                "# Base module\n\n"
                "Defines $f(n) = \\frac{n(n + 1)}{2}$.\n"
                "-/\n\n"
                "/-- Returns **twice** $x$, i.e. $2 \\cdot x$. -/\n"
                "@[simp]\n"
                "def dbl (x : Nat) : Nat :=\n"
                "  x + x\n\n"
                "-- Line comment doc for `dbl_zero`.\n"
                "theorem dbl_zero : dbl 0 = 0 := rfl\n"
            ),
        }
        fake_axle._extract_documents_by_marker = {
            "def dbl": {
                "dbl": make_document(
                    "dbl",
                    kind="def",
                    line_pos=12,
                    end_line_pos=13,
                    signature="def dbl (x : Nat) : Nat",
                ),
                "dbl_zero": make_document(
                    "dbl_zero",
                    kind="theorem",
                    line_pos=16,
                    end_line_pos=16,
                    signature="theorem dbl_zero : dbl 0 = 0 := rfl",
                    local_type_dependencies=["dbl"],
                ),
            },
        }
        root = make_project(tmp_path, NO_TARGETS_CONFIG, files)
        monkeypatch.chdir(root)
        assert runner.invoke(main, ["compile"]).exit_code == 0

        _output, html_text = run_graph(root)
        assert html_text.count("</script>") == 4
        assert KATEX_CSS_URL in html_text
        assert KATEX_JS_URL in html_text
        assert "window.katex.render" in html_text
        assert "renderMathIn" in html_text
        data = graph_data(html_text)

        file_node = by_id(data, "file:M.Base")
        assert "Base module" in file_node["doc"]
        assert "<h1>Base module</h1>" in file_node["doc_html"]
        assert '<span class="math-inline" data-latex="f(n) = \\frac{n(n + 1)}{2}">' in file_node["doc_html"]
        assert "def dbl (x : Nat) : Nat :=" in file_node["code"]

        dbl_node = by_id(data, "decl:M.Base:dbl")
        assert dbl_node["module"] == "M"
        assert "**twice**" in dbl_node["doc"]
        assert "<strong>twice</strong>" in dbl_node["doc_html"]
        assert '<span class="math-inline" data-latex="2 \\cdot x">' in dbl_node["doc_html"]
        assert dbl_node["code"].startswith("@[simp]\ndef dbl")
        assert dbl_node["code_start_line"] == 10

        zero_node = by_id(data, "decl:M.Base:dbl_zero")
        assert zero_node["module"] == "M"
        assert zero_node["doc"] == "Line comment doc for `dbl_zero`."
        assert '<code class="md-inline-code">dbl_zero</code>' in zero_node["doc_html"]
        assert zero_node["code"] == "theorem dbl_zero : dbl 0 = 0 := rfl"
        assert zero_node["code_start_line"] == 15

        # UI controls for gradual scroll zoom, draggable/expandable drawer,
        # compact top search, autocomplete, serif typography, subgraph
        # isolation, doc rendering, unified Source section, and module-grouped chips.
        assert "wheelSensitivity: 0.22" in html_text
        assert '"Source Serif 4"' in html_text
        assert "#legend { position: fixed; z-index: 30;" in html_text
        assert "#tooltip { position: fixed; z-index: 8;" in html_text
        assert '<div id="legend" class="drawer dock-bottom">' in html_text
        assert 'var dockMode = "bottom";' in html_text
        assert 'id="toggle-dock"' in html_text
        assert 'id="toggle-full"' in html_text
        assert 'id="toggle-drawer"' in html_text
        drawer_chunk = html_text.split('<div id="legend" class="drawer dock-bottom">', 1)[1].split(
            '<script type="application/json"', 1
        )[0]
        assert 'id="drawer-resizer"' in drawer_chunk
        assert 'id="search-nodes"' in drawer_chunk
        assert 'id="legend-panel"' not in drawer_chunk
        assert 'id="inspector"' in drawer_chunk
        assert "#legend.full" in html_text
        assert "drawerFull" in html_text
        assert "applyDragSize" in html_text
        assert 'id="search-autocomplete"' in html_text
        assert 'id="search-count"' in html_text
        assert "dock-side" in html_text
        assert "#legend.dock-side { top: 0; left: 0; bottom: 0;" in html_text
        assert "#legend.dock-side > .drawer-resizer { cursor: ew-resize; width: 8px; top: 0; bottom: 0; right: 0; }" in html_text
        assert "dock-bottom" in html_text
        assert "insp-subgraph-view" in html_text
        assert "subgraph-canvas" in html_text
        assert "insp-doc" in html_text
        assert "insp-code" in html_text
        assert '<span class="insp-sec">Source</span>' in html_text
        assert ">Source Code<" not in html_text
        assert ">Signature<" not in html_text
        render_insp_src = html_text.split("function renderInspector(node)", 1)[1].split(
            "function selectElement(target)", 1
        )[0]
        assert render_insp_src.index('<span class="insp-sec">Source</span>') < render_insp_src.index(
            '"Depends on"'
        )
        assert render_insp_src.index("Source (' + lineCount + ' lines)") < render_insp_src.index(
            '"Imports"'
        )
        assert "nodeModuleOf" in html_text
        assert "insp-mod-group" in html_text
        assert "insp-mod-label" in html_text
        assert "Transitive upstream" in html_text
        assert "Transitive downstream" in html_text
        for cls in (
            ".hljs-keyword",
            ".hljs-title",
            ".hljs-built_in",
            ".hljs-comment",
            ".hljs-meta",
            ".hljs-doctag",
        ):
            assert cls in html_text
        assert "highlightLeanLines" in html_text
        assert "highlightLeanInline" in html_text

    def test_stamps_include_sigs_and_link_to_axle_share_urls(
        self, graph_project: Path
    ) -> None:
        from axle_build_tool.manifest import save_manifest

        manifest = load_manifest(graph_project)
        now = datetime(2026, 1, 1, tzinfo=timezone.utc)
        nodes = []
        for node in manifest.nodes:
            decls = []
            for decl in node.declarations:
                if decl.name == "base_thm":
                    decl = decl.model_copy(
                        update={
                            "checked_sig": "c" * 32,
                            "checked_at": now,
                            "checked_request_id": "req-chk-1",
                            "verified_sig": "v" * 32,
                            "verified_at": now,
                            "verified_request_id": "req-ver-1",
                        }
                    )
                decls.append(decl)
            nodes.append(node.model_copy(update={"declarations": decls}))
        save_manifest(manifest.model_copy(update={"nodes": nodes}), graph_project)

        _output, html_text = run_graph(graph_project)
        data = graph_data(html_text)
        base_thm = by_id(data, "decl:M.A:base_thm")
        assert base_thm["checked_sig"] == "c" * 32
        assert base_thm["checked_request_id"] == "req-chk-1"
        assert base_thm["verified_sig"] == "v" * 32
        assert base_thm["verified_request_id"] == "req-ver-1"
        assert "cccccccc" in base_thm["checked_stamp"]
        assert "vvvvvvvv" in base_thm["verified_stamp"]

        base_def = by_id(data, "decl:M.A:base")
        assert base_def["closure_verified_request_id"] == "req-ver-1"

        assert "stamp-link" in html_text
        assert "axleShareUrl" in html_text
        assert "//axle.axiommath.ai/" in html_text
        assert '"verify_proof"' in html_text
        assert '"check"' in html_text


class TestGraphServe:
    """Tests for `axbt graph --serve [--port PORT]`."""

    def test_port_without_serve_does_not_start_server(
        self, graph_project: Path, monkeypatch
    ) -> None:
        import axle_build_tool.cli as cli_mod

        called = False

        def fail_if_called(*args, **kwargs):
            nonlocal called
            called = True
            raise AssertionError("create_graph_server should not be called without --serve")

        monkeypatch.setattr(cli_mod, "create_graph_server", fail_if_called)
        result = runner.invoke(main, ["graph", "--port", "4199"])
        assert result.exit_code == 0, result.output
        assert not called
        assert "Wrote graph to" in result.output
        assert "Serving graph" not in result.output

    def test_serve_prints_local_and_network_urls_and_handles_keyboard_interrupt(
        self, graph_project: Path, monkeypatch
    ) -> None:
        import axle_build_tool.cli as cli_mod
        from axle_build_tool.graph import DEFAULT_GRAPH_HOST, DEFAULT_GRAPH_PORT

        captured: dict[str, object] = {}

        class FakeServer:
            def __init__(self, graph_file: Path, host: str, port: int) -> None:
                captured["graph_file"] = graph_file
                captured["host"] = host
                captured["port"] = port
                self.server_address = (host, port)
                self.closed = False

            def serve_forever(self) -> None:
                captured["served"] = True
                raise KeyboardInterrupt

            def server_close(self) -> None:
                self.closed = True
                captured["closed"] = True

        monkeypatch.setattr(cli_mod, "create_graph_server", FakeServer)
        monkeypatch.setattr(cli_mod, "detect_network_ips", lambda: ["10.0.0.42"])

        result = runner.invoke(main, ["graph", "--serve"])
        assert result.exit_code == 0, result.output
        assert captured["host"] == DEFAULT_GRAPH_HOST
        assert captured["port"] == DEFAULT_GRAPH_PORT
        assert captured["graph_file"] == graph_project / ".axbt" / "graph.html"
        assert captured.get("served") is True
        assert captured.get("closed") is True
        assert "Wrote graph to" in result.output
        assert "Serving graph on 0.0.0.0:4099" in result.output
        assert "http://127.0.0.1:4099" in result.output
        assert "http://10.0.0.42:4099" in result.output
        assert "Stopped graph server." in result.output

    def test_serve_custom_port(self, graph_project: Path, monkeypatch) -> None:
        import axle_build_tool.cli as cli_mod

        class FakeServer:
            def __init__(self, graph_file: Path, host: str, port: int) -> None:
                self.server_address = (host, port)

            def serve_forever(self) -> None:
                raise KeyboardInterrupt

            def server_close(self) -> None:
                pass

        monkeypatch.setattr(cli_mod, "create_graph_server", FakeServer)
        monkeypatch.setattr(cli_mod, "detect_network_ips", lambda: ["10.0.0.77"])

        result = runner.invoke(main, ["graph", "--serve", "--port", "4567"])
        assert result.exit_code == 0, result.output
        assert "Serving graph on 0.0.0.0:4567" in result.output
        assert "http://127.0.0.1:4567" in result.output
        assert "http://10.0.0.77:4567" in result.output

    def test_create_graph_server_serves_generated_html_and_404s_other_paths(
        self, graph_project: Path
    ) -> None:
        import io
        from axle_build_tool.graph import create_graph_server

        class _InMemorySocket:
            def __init__(self, request_bytes: bytes) -> None:
                self._rfile = io.BytesIO(request_bytes)
                self.wfile = io.BytesIO()

            def makefile(self, mode: str, *args, **kwargs):
                if "r" in mode:
                    return self._rfile
                return self.wfile

            def sendall(self, data: bytes) -> None:
                self.wfile.write(data)

        def dispatch(server, method: str, path: str) -> tuple[str, bytes]:
            raw_req = f"{method} {path} HTTP/1.1\r\nHost: localhost\r\n\r\n".encode("ascii")
            sock = _InMemorySocket(raw_req)
            server.RequestHandlerClass(sock, ("127.0.0.1", 50000), server)
            raw_resp = sock.wfile.getvalue()
            header_bytes, _, body_bytes = raw_resp.partition(b"\r\n\r\n")
            return header_bytes.decode("iso-8859-1"), body_bytes

        _output, expected_html = run_graph(graph_project)
        graph_file = graph_project / ".axbt" / "graph.html"
        server = create_graph_server(
            graph_file, host="127.0.0.1", port=4099, bind_and_activate=False
        )

        for path in ("/", "/graph.html", "/index.html", "/?q=base"):
            headers, body = dispatch(server, "GET", path)
            assert headers.startswith("HTTP/1.0 200 OK")
            assert "Content-Type: text/html; charset=utf-8" in headers
            assert body.decode("utf-8") == expected_html

        headers, head_body = dispatch(server, "HEAD", "/")
        assert headers.startswith("HTTP/1.0 200 OK")
        assert head_body == b""

        headers, not_found_body = dispatch(server, "GET", "/manifest.json")
        assert headers.startswith("HTTP/1.0 404 Not Found")
        assert not_found_body == b"Not Found"

    def test_detect_network_ips_prefers_10_dot_private_and_excludes_loopback(
        self, monkeypatch
    ) -> None:
        import socket
        import subprocess
        import axle_build_tool.graph as graph_mod

        class FakeUdpSocket:
            def __init__(self, target_ip: str) -> None:
                self._ip = target_ip

            def __enter__(self):
                return self

            def __exit__(self, *exc):
                return False

            def connect(self, addr):
                target, _port = addr
                if target.startswith("10."):
                    self._ip = "10.0.0.19"
                elif target.startswith("192.168."):
                    self._ip = "192.168.1.5"
                else:
                    self._ip = "127.0.0.1"

            def getsockname(self):
                return (self._ip, 12345)

        monkeypatch.setattr(
            socket,
            "socket",
            lambda *args, **kwargs: FakeUdpSocket("127.0.0.1"),
        )
        monkeypatch.setattr(
            socket,
            "getaddrinfo",
            lambda *args, **kwargs: [
                (socket.AF_INET, socket.SOCK_STREAM, 0, "", ("127.0.0.1", 0)),
                (socket.AF_INET, socket.SOCK_STREAM, 0, "", ("169.254.1.2", 0)),
                (socket.AF_INET, socket.SOCK_STREAM, 0, "", ("10.0.0.19", 0)),
            ],
        )
        monkeypatch.setattr(
            subprocess,
            "run",
            lambda *args, **kwargs: subprocess.CompletedProcess(
                args=["ifconfig"],
                returncode=0,
                stdout="lo0:\n\tinet 127.0.0.1\nen0:\n\tinet 10.0.0.88 netmask 0xffffff00\n",
                stderr="",
            ),
        )
        ips = graph_mod.detect_network_ips()
        assert ips == ["10.0.0.19", "10.0.0.88", "192.168.1.5"]
