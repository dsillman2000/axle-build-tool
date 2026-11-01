"""CLI-level tests for `axbt graph`, driven through the real entry point.

The suite stays offline: the Cytoscape.js CDN URL is asserted as text,
never fetched, and the embedded graph data is parsed straight out of
the generated page's JSON block.
"""

from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path

import pytest
from click.testing import CliRunner

from axle_build_tool import main
from axle_build_tool.graph import rollup_state, state_of
from axle_build_tool.graph import _layout_positions
from axle_build_tool.manifest import (
    MANIFEST_VERSION,
    ExtractedDecl,
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

        # The only external references: the pinned, SRI-hashed CDN
        # scripts (Cytoscape core + the fcose dependency chain).
        assert (
            "https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.31.0/cytoscape.min.js"
            in html_text
        )
        assert (
            "https://cdn.jsdelivr.net/npm/layout-base@2.0.1/layout-base.js"
            in html_text
        )
        assert (
            "https://cdn.jsdelivr.net/npm/cose-base@2.2.0/cose-base.js"
            in html_text
        )
        assert (
            "https://cdn.jsdelivr.net/npm/cytoscape-fcose@2.2.0/cytoscape-fcose.js"
            in html_text
        )
        assert 'integrity="' in html_text and 'crossorigin="anonymous"' in html_text
        # No other network references anywhere in the page.
        urls = re.findall(r"https?://[^\s\"']+ ", html_text)
        allowed = (
            "https://cdnjs.cloudflare.com",
            "https://cdn.jsdelivr.net/npm/layout-base",
            "https://cdn.jsdelivr.net/npm/cose-base",
            "https://cdn.jsdelivr.net/npm/cytoscape-fcose",
        )
        assert urls == [] or all(url.startswith(allowed) for url in urls)

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
        # The style sheet drives the split (round default -> circles for
        # the proof kinds via data-kind selectors).
        assert 'shape: "roundrectangle" } }' in html_text
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

        # Exactly six script elements: the four pinned CDN scripts
        # (Cytoscape + its fcose dependency chain), the data block, and
        # the application script.
        assert html_text.count("</script>") == 6
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
        assert "✱" in html_text

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

        for state in ("verified", "checked", "done", "unchecked", "empty"):
            assert f"chip {state}" in html_text
        assert "outcome stamps" in html_text
        assert "never verifiable" in html_text

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

    def test_declarations_stack_top_to_bottom_inside_their_file(self) -> None:
        files = [self.node("Core.CoreFile", (), ["beta", "alpha"])]
        positions, _cells = _layout_positions(files)
        alpha, beta = positions["decl:Core.CoreFile:alpha"], positions["decl:Core.CoreFile:beta"]
        assert alpha["y"] < beta["y"]  # sorted by declaration name
        assert alpha["x"] == beta["x"]  # one aligned dot-list

    def test_cluster_stacking_leaves_declaration_free_files_in_place(
        self,
    ) -> None:
        files = [self.node("Core.CoreFile", ()), self.node("Core.Empty", ("Core.CoreFile",))]
        positions, _cells = _layout_positions(files)
        # Both files share their module column; the declaration-free one
        # is placed below its importing sibling without overlapping it.
        assert positions["file:Core.Empty"]["y"] > positions["file:Core.CoreFile"]["y"]

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
