/**
 * Runtime harness for axbt's generated graph page.
 *
 * Usage: node graph_runtime_harness.js <graph.html> <cytoscape.min.js>
 *              [cytoscape-fcose-package-path]
 *
 * Runs the page's own application script against a REAL Cytoscape
 * (headless — the container constructor line is patched to
 * `headless: true`), registering the pinned fcose force layout when
 * its package path is supplied (the package's runtime deps resolve via
 * sibling `node_modules` dirs the test lays down from the downloaded
 * CDN files). Asserts what the browser would have: every node/edge
 * ingests, compound containment resolves, states arrive as classes,
 * and — with fcose loaded — the per-file force pass moved declarations
 * and the renormalization kept every member inside its cluster cell.
 * Also exercises the no-fcose degradation path when the third argument
 * is omitted. Catches the "renders a legend but no data" class of bug
 * that text assertions cannot see.
 */
"use strict";
const fs = require("fs");

const [pagePath, cytoscapePath, fcosePath] = process.argv.slice(2);
if (!pagePath || !cytoscapePath) {
  console.error("usage: node graph_runtime_harness.js <graph.html> <cytoscape.min.js> [cytoscape-fcose-package-path]");
  process.exit(2);
}
const cytoscape = require(cytoscapePath);
// fcose's UMD build reads the `cytoscape` global at load time (the
// browser's script tag order provides it); mirror that here before
// requiring the extension.
globalThis.cytoscape = cytoscape;
const fcose = fcosePath ? require(fcosePath) : null;

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

// The legend controls behave like real widgets: `checked` state and
// recorded change/click listeners the harness can fire later.
const toggle = { checked: false, listeners: {}, style: {} };
toggle.addEventListener = (name, handler) => {
  toggle.listeners[name] = handler;
};
toggle.fireChange = () => {
  if (toggle.listeners.change) { toggle.listeners.change(); }
};
const resetButton = { listeners: {}, style: {} };
resetButton.addEventListener = (name, handler) => {
  resetButton.listeners[name] = handler;
};
resetButton.fireClick = () => {
  if (resetButton.listeners.click) { resetButton.listeners.click(); }
};

// A delegating wrapper so the harness keeps the constructed instance
// while the page script calls `window.cytoscape` (and its `.use`)
// exactly as the browser would.
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
    if (id === "graph-data") {
      return { id, textContent: docMatch[1], style: {} };
    }
    if (id === "toggle-decl-edges") {
      return toggle;
    }
    if (id === "reset-positions") {
      return resetButton;
    }
    return { id, style: {} };
  },
};

try {
  new Function("window", "document", script)(
    { cytoscape: harnessCytoscape, cytoscapeFcose: fcose },
    documentStub
  );
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
// Shapes split by verifiability: verifiable kinds render as circles
// (ellipse), never-verifiable declarations as rounded squares. Since a
// headless render cannot draw shapes, this asserts the data plumbing
// (every declaration carries its kind) plus the page's shape rules.
const verifiableKinds = new Set(["theorem", "lemma", "example"]);
const shapeMismatches = [];
for (const node of payload.nodes) {
  if (node.group !== "declaration") {
    continue;
  }
  const nodeKind = cy.getElementById(node.id).data("kind");
  if (nodeKind !== node.kind || !node.kind) {
    shapeMismatches.push(`${node.id} carries kind ${JSON.stringify(nodeKind)} (manifest: ${JSON.stringify(node.kind)})`);
  }
  void verifiableKinds;
}
if (shapeMismatches.length) {
  errors.push(`declaration kinds not plumbed: ${shapeMismatches.join("; ")}`);
}
const shapePageRules =
  page.includes("node[kind='theorem'], node[kind='lemma'], node[kind='example']") &&
  page.includes('shape: "roundrectangle"');
if (!shapePageRules) {
  errors.push("the page's style sheet does not split declaration shapes by kind");
}
// Id lookups and edge connectivity work the way the page's handlers do.
for (const element of payload.nodes.concat(payload.edges)) {
  if (cy.getElementById(element.id).length === 0) {
    errors.push(`element not ingested: ${element.id}`);
  }
}

// The per-file force pass: declarations moved off their preset stacks
// and the renormalization kept every member inside its cell.
const cellsById = {};
const clusterSizes = {};
for (const node of payload.nodes) {
  if (node.group === "file" && node.cell) {
    cellsById[node.id] = node.cell;
  }
  if (node.group === "declaration") {
    clusterSizes[node.parent] = (clusterSizes[node.parent] || 0) + 1;
  }
}
let moved = 0;
let spreadable = 0;
let spreadableClusters = 0;
for (const node of payload.nodes) {
  if (node.group !== "declaration") {
    continue;
  }
  const cell = cellsById[node.parent];
  const now = cy.getElementById(node.id).position();
  const hasCell = cell !== undefined;
  const movedHere =
    Math.abs(now.x - node.position.x) + Math.abs(now.y - node.position.y) > 0.5;
  if (hasCell) {
    spreadable += 1;
    if (movedHere) {
      moved += 1;
    }
    if (fcose) {
      if (
        now.x < cell.x1 - 4 ||
        now.x > cell.x2 + 4 ||
        now.y < cell.y1 - 4 ||
        now.y > cell.y2 + 4
      ) {
        errors.push(
          `declaration ${node.id} escaped its cell: (${now.x}, ${now.y}) not within (${cell.x1}, ${cell.y1})-(${cell.x2}, ${cell.y2})`
        );
      }
    }
  }
}
for (const fileId of Object.keys(clusterSizes)) {
  if (cellsById[fileId] !== undefined && clusterSizes[fileId] >= 2) {
    spreadableClusters += 1;
  }
}
if (fcose && spreadableClusters > 0 && moved === 0) {
  errors.push("the per-file fcose layout never moved a declaration");
}

// --- The declaration-edge checkbox: hidden by default -------------------
function report(message) {
  console.log(`  toggle: ${message}`);
}
const dependsEdges = cy.edges('[kind = "depends"]');
const toggleEdgeError = (message) => {
  errors.push(`toggle: ${message}`);
};

if (dependsEdges.length && toggle.listeners.change) {
  // 1. Default (un-ticked): every depends-edge is hidden.
  const hiddenAtStart = dependsEdges.filter((edge) => edge.hasClass("hidden"));
  if (hiddenAtStart.length !== dependsEdges.length) {
    toggleEdgeError("the default (unticked) did not hide every depends-edge");
  } else {
    report("unticked by default: all depends-edges hidden");
  }

  // 2. Ticking shows everything again.
  toggle.checked = true;
  toggle.fireChange();
  if (dependsEdges.some((edge) => edge.hasClass("hidden"))) {
    toggleEdgeError("ticking did not unhide the depends-edges");
  } else {
    report("ticked: arrows visible");
  }

  // 3. Un-ticking hides them again; a tap then reveals the tapped
  // declaration's dependency neighborhood (both direction sides) while
  // everything else stays hidden.
  toggle.checked = false;
  toggle.fireChange();
  const tapped = dependsEdges.first().source();
  tapped.emit("tap");
  const connected = tapped.connectedEdges('[kind = "depends"]');
  const revealed = connected.filter((edge) => !edge.hasClass("hidden"));
  if (revealed.length !== connected.length) {
    toggleEdgeError(
      `tapping '${tapped.data("id")}' revealed ${revealed.length} of its ${connected.length} dependency edges`
    );
  }
  const outsideStillHidden = dependsEdges
    .filter((edge) => connected.filter((mine) => mine.id() === edge.id()).length === 0)
    .every((edge) => edge.hasClass("hidden"));
  if (!outsideStillHidden) {
    toggleEdgeError("edges outside the tapped neighborhood lost their hidden treatment");
  }
  if (revealed.length) {
    report(`tap-reveal works: ${revealed.length} edges shown for the tapped declaration`);
  }

  // 4. Clicking the background restores the hidden treatment.
  cy.emit("tap");
  if (!dependsEdges.every((edge) => edge.hasClass("hidden"))) {
    toggleEdgeError("a background tap did not restore the hidden treatment");
  } else {
    report("background tap: reveal collapses back to hidden");
  }

  // 5. Ticking once more shows everything again.
  toggle.checked = true;
  toggle.fireChange();
  if (dependsEdges.some((edge) => edge.hasClass("hidden"))) {
    toggleEdgeError("re-ticking did not unhide the depends-edges");
  }
  toggle.checked = false;
  toggle.fireChange(); // leave the page in its default state
}

// --- Draggability and the reset control ---------------------------------
// Nodes AND compounds must be grabbable (a misplaced `autoungrabify`
// would make the whole interaction moot).
const firstCompound = cy.nodes('[group = "file"]').first();
const firstDeclaration = cy.nodes('[group = "declaration"]').first();
if (!firstDeclaration.grabbable() || (firstCompound.length && !firstCompound.grabbable())) {
  errors.push("nodes/compounds are not grabbable (dragging is disabled)");
}

// Snapshot the freshly-spread positions; drag both a declaration and a
// file compound (a compound drag must carry its children), then reset.
const snapshot = {};
cy.nodes().forEach((node) => {
  if (!node.isParent()) {
    snapshot[node.id()] = {
      x: node.position("x"),
      y: node.position("y"),
    };
  }
});
if (firstDeclaration.length && firstCompound.length && resetButton.listeners.click) {
  firstDeclaration.position({ x: firstDeclaration.position("x") + 40, y: firstDeclaration.position("y") + 40 });
  firstCompound.position({ x: firstCompound.position("x") + 120, y: firstCompound.position("y") + 120 });
  const draggedChild = firstCompound.children().first();
  if (draggedChild.length && Math.abs(draggedChild.position("x") - payload.nodes.find((n) => n.id === draggedChild.id()).position.x) < 119) {
    errors.push("dragging a file compound did not move its declarations");
  }
  resetButton.fireClick();
  cy.nodes().forEach((node) => {
    if (node.isParent()) { return; }
    const home = snapshot[node.id()];
    if (Math.abs(node.position("x") - home.x) > 0.5 || Math.abs(node.position("y") - home.y) > 0.5) {
      errors.push(`reset layout left ${node.id()} away from its spread position`);
    }
  });
}

if (errors.length) {
  errors.forEach((error) => console.error(`- ${error}`));
  process.exit(1);
}
console.log(
  `OK: ${cy.nodes().length} nodes, ${cy.edges().length} edges ingested; containment, states, ids, cells resolve (${moved} declarations re-spread${fcose ? ", fcose replayed" : ", degraded preset"}; ${dependsEdges.length} toggle-able depends-edges checked)`
);
