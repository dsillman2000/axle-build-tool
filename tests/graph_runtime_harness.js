/**
 * Runtime harness for axbt's generated graph page.
 *
 * Usage: node graph_runtime_harness.js <graph.html> <cytoscape.min.js>
 *
 * Runs the page's own application script against a REAL Cytoscape
 * (headless — the container constructor line is patched to
 * `headless: true`). Asserts what the browser would have: every
 * node/edge ingests, compound containment resolves, states arrive as
 * classes, build-time positions are used verbatim and sit inside their
 * file cells, the edge toggles / tap-highlight / search / inspector
 * controls behave, and the reset control restores the layout. Catches
 * the "renders a legend but no data" class of bug that text assertions
 * cannot see.
 */
"use strict";
const fs = require("fs");

const [pagePath, cytoscapePath] = process.argv.slice(2);
if (!pagePath || !cytoscapePath) {
  console.error("usage: node graph_runtime_harness.js <graph.html> <cytoscape.min.js>");
  process.exit(2);
}
const cytoscape = require(cytoscapePath);

const page = fs.readFileSync(pagePath, "utf8");
const docMatch = page.match(/<script type="application\/json" id="graph-data">(.*?)<\/script>/s);
// The application script is the last <script> in the page body.
const jsMatch = page.match(/<script>\n([\s\S]*?)\n<\/script>\n<\/body>/);
if (!docMatch || !jsMatch) {
  console.error("page missing the data block or application script");
  process.exit(2);
}

// Patch the (browser-only) container wiring to headless mode so the
// page's own script can run here — same construction, no DOM.
const script = jsMatch[1].replace(
  'container: document.getElementById("graph")',
  "headless: true"
);

// Legend widgets behave like real controls: recorded listeners the
// harness can fire later.
function makeControl(extra) {
  const control = Object.assign({ listeners: {}, style: {}, value: "", checked: false }, extra);
  control.addEventListener = (name, handler) => {
    control.listeners[name] = handler;
  };
  control.fire = (name, event) => {
    if (control.listeners[name]) { control.listeners[name](event || {}); }
  };
  return control;
}
const declToggle = makeControl();
const transToggle = makeControl();
const resetButton = makeControl();
const searchInput = makeControl();
const inspector = makeControl({
  innerHTML: "",
  querySelectorAll() { return []; },
});

let cy = null;
const harnessCytoscape = Object.assign(
  function (options) {
    cy = cytoscape(options);
    return cy;
  },
  { use: cytoscape.use.bind(cytoscape) }
);
const documentStub = {
  getElementById(id) {
    switch (id) {
      case "graph-data": return { id, textContent: docMatch[1], style: {} };
      case "toggle-decl-edges": return declToggle;
      case "toggle-transitive-edges": return transToggle;
      case "reset-positions": return resetButton;
      case "search-nodes": return searchInput;
      case "inspector": return inspector;
      default: return { id, style: {} };
    }
  },
};

try {
  new Function("window", "document", script)({ cytoscape: harnessCytoscape }, documentStub);
} catch (error) {
  console.error("page script threw:", error);
  process.exit(2);
}
if (cy === null) {
  console.error("page script never constructed a Cytoscape instance");
  process.exit(2);
}

const payload = JSON.parse(docMatch[1]);
const errors = [];
for (const pair of [
  ["nodes", payload.nodes.length, cy.nodes().length],
  ["edges", payload.edges.length, cy.edges().length],
]) {
  if (pair[1] !== pair[2]) {
    errors.push(`expected ${pair[1]} ${pair[0]}, real Cytoscape ingested ${pair[2]}`);
  }
}
// Containment resolved: no declaration/file left unparented.
const unparented = cy
  .nodes('[group = "declaration"], [group = "file"]')
  .filter((node) => node.parent().length === 0);
if (unparented.length !== 0) {
  errors.push(`${unparented.length} member node(s) left unparented`);
}
// States arrived as classes.
const states = ["verified", "checked", "done", "unchecked", "empty"];
const stateSum = states.reduce((total, state) => total + cy.nodes(`node.${state}`).length, 0);
if (stateSum !== cy.nodes().length) {
  errors.push(`state classes cover ${stateSum} of ${cy.nodes().length} nodes`);
}
// Every declaration carries its kind, and the style sheet splits the
// shapes by verifiability (ellipses vs solid rectangles).
for (const node of payload.nodes) {
  if (node.group !== "declaration") { continue; }
  const nodeKind = cy.getElementById(node.id).data("kind");
  if (nodeKind !== node.kind || !node.kind) {
    errors.push(`${node.id} carries kind ${JSON.stringify(nodeKind)} (manifest: ${JSON.stringify(node.kind)})`);
  }
}
if (
  !page.includes("node[kind='theorem'], node[kind='lemma'], node[kind='example']") ||
  !page.includes('shape: "ellipse"') ||
  !page.includes('shape: "rectangle"')
) {
  errors.push("the page's style sheet does not split declaration shapes by kind");
}
for (const element of payload.nodes.concat(payload.edges)) {
  if (cy.getElementById(element.id).length === 0) {
    errors.push(`element not ingested: ${element.id}`);
  }
}

// Build-time layout: positions are used verbatim and every declaration
// sits inside its file's cell.
const cellsById = {};
for (const node of payload.nodes) {
  if (node.group === "file" && node.cell) { cellsById[node.id] = node.cell; }
}
for (const node of payload.nodes) {
  if (node.group !== "declaration") { continue; }
  const now = cy.getElementById(node.id).position();
  if (Math.abs(now.x - node.position.x) > 0.5 || Math.abs(now.y - node.position.y) > 0.5) {
    errors.push(`declaration ${node.id} moved off its build-time position`);
  }
  const cell = cellsById[node.parent];
  if (cell && (now.x < cell.x1 || now.x > cell.x2 || now.y < cell.y1 || now.y > cell.y2)) {
    errors.push(`declaration ${node.id} outside its cell`);
  }
}

// --- Edge toggles: depends-edges and transitive imports hidden by default
const dependsEdges = cy.edges('[kind = "depends"]');
const transitiveEdges = cy.edges("edge.transitive");
function report(message) { console.log(`  toggle: ${message}`); }
const toggleError = (message) => errors.push(`toggle: ${message}`);

if (dependsEdges.length) {
  if (dependsEdges.filter((e) => e.hasClass("hidden")).length !== dependsEdges.length) {
    toggleError("the default (unticked) did not hide every depends-edge");
  }
  declToggle.checked = true;
  declToggle.fire("change");
  if (dependsEdges.some((e) => e.hasClass("hidden"))) {
    toggleError("ticking did not unhide the depends-edges");
  }
  declToggle.checked = false;
  declToggle.fire("change");

  // A tap on a declaration reveals its transitive dependency cone only.
  const tapped = dependsEdges.first().source();
  tapped.emit("tap");
  const connected = tapped.connectedEdges('[kind = "depends"]');
  if (connected.filter((e) => !e.hasClass("hidden")).length !== connected.length) {
    toggleError(`tapping '${tapped.id()}' did not reveal its dependency edges`);
  }
  if (!tapped.hasClass("selected-node")) {
    toggleError("tapped declaration was not marked selected");
  }
  if (!inspector.innerHTML.includes(tapped.data("full_name"))) {
    toggleError("the inspector did not describe the tapped declaration");
  }
  cy.emit("tap");
  if (!dependsEdges.every((e) => e.hasClass("hidden"))) {
    toggleError("a background tap did not restore the hidden treatment");
  }
  report(`depends-edges: ${dependsEdges.length} toggle/tap/background checked`);
}
if (transitiveEdges.length) {
  if (!transitiveEdges.every((e) => e.hasClass("hidden"))) {
    toggleError("transitive imports are not hidden by default");
  }
  transToggle.checked = true;
  transToggle.fire("change");
  if (transitiveEdges.some((e) => e.hasClass("hidden"))) {
    toggleError("ticking did not unhide the transitive imports");
  }
  transToggle.checked = false;
  transToggle.fire("change");
  report(`transitive imports: ${transitiveEdges.length} toggle checked`);
}

// --- Search: matches are highlighted, the rest of the declarations dim
const sampleDecl = cy.nodes('[group = "declaration"]').first();
if (sampleDecl.length) {
  searchInput.value = sampleDecl.data("label");
  searchInput.fire("input");
  if (!sampleDecl.hasClass("highlighted")) {
    errors.push("search did not highlight the matching declaration");
  }
  searchInput.value = "";
  searchInput.fire("input");
  if (cy.elements(".highlighted, .dimmed").length !== 0) {
    errors.push("clearing the search left highlighted/dimmed elements");
  }
}

// --- Draggability and the reset control
const firstCompound = cy.nodes('[group = "file"]').first();
const firstDeclaration = cy.nodes('[group = "declaration"]').first();
if (!firstDeclaration.grabbable() || (firstCompound.length && !firstCompound.grabbable())) {
  errors.push("nodes/compounds are not grabbable (dragging is disabled)");
}
const snapshot = {};
cy.nodes().forEach((node) => {
  if (!node.isParent()) {
    snapshot[node.id()] = { x: node.position("x"), y: node.position("y") };
  }
});
if (firstDeclaration.length && firstCompound.length && resetButton.listeners.click) {
  firstDeclaration.position({ x: firstDeclaration.position("x") + 40, y: firstDeclaration.position("y") + 40 });
  firstCompound.position({ x: firstCompound.position("x") + 120, y: firstCompound.position("y") + 120 });
  const draggedChild = firstCompound.children().first();
  if (draggedChild.length && Math.abs(draggedChild.position("x") - payload.nodes.find((n) => n.id === draggedChild.id()).position.x) < 119) {
    errors.push("dragging a file compound did not move its declarations");
  }
  resetButton.fire("click");
  cy.nodes().forEach((node) => {
    if (node.isParent()) { return; }
    const home = snapshot[node.id()];
    if (Math.abs(node.position("x") - home.x) > 0.5 || Math.abs(node.position("y") - home.y) > 0.5) {
      errors.push(`reset layout left ${node.id()} away from its layout position`);
    }
  });
}

if (errors.length) {
  errors.forEach((error) => console.error(`- ${error}`));
  process.exit(1);
}
console.log(
  `OK: ${cy.nodes().length} nodes, ${cy.edges().length} edges ingested; containment, states, ids, cells resolve (static layout replayed; ${dependsEdges.length} depends-edges and ${transitiveEdges.length} transitive imports checked)`
);
