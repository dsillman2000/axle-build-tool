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

// The legend checkbox behaves like a real input: `checked` state and a
// recorded change listener the harness can fire later to drive the
// reveal/hide rules.
const toggle = { checked: true, listeners: {}, style: {}, value: "" };
toggle.addEventListener = (name, handler) => {
  toggle.listeners[name] = handler;
};
toggle.fireChange = () => {
  if (toggle.listeners.change) { toggle.listeners.change(); }
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
const states = ["verified", "checked", "unchecked", "empty"];
const stateSum = states.reduce((total, state) => total + cy.nodes(`node.${state}`).length, 0);
if (stateSum !== cy.nodes().length) {
  errors.push(`state classes cover ${stateSum} of ${cy.nodes().length} nodes`);
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

// --- The declaration-edge checkbox: reveal / hide / restore --------------
function report(message) {
  console.log(`  toggle: ${message}`);
}
const dependsEdges = cy.edges('[kind = "depends"]');
const toggleEdgeError = (message) => {
  errors.push(`toggle: ${message}`);
};

if (dependsEdges.length && toggle.listeners.change) {
  // 1. Default (checked): no depends-edge is hidden.
  if (dependsEdges.some((edge) => edge.hasClass("hidden"))) {
    toggleEdgeError("edges are hidden while the box is ticked");
  } else {
    report("ticked by default: all depends-edges visible");
  }

  // 2. Un-tick: every depends-edge hides.
  toggle.checked = false;
  toggle.fireChange();
  const hiddenAll = dependsEdges.every((edge) => edge.hasClass("hidden"));
  if (!hiddenAll) {
    toggleEdgeError("un-ticking did not hide every depends-edge");
  } else {
    report("un-ticked: every depends-edge hidden");
  }

  // 3. Click a declaration with dependencies: its neighborhood (the
  // dependency side AND the dependents side) reveals while the rest
  // stays hidden.
  const tapped = dependsEdges.first().source();
  tapped.emit("tap");
  const revealed = tapped
    .connectedEdges('[kind = "depends"]')
    .filter((edge) => !edge.hasClass("hidden"));
  if (revealed.length !== tapped.connectedEdges('[kind = "depends"]').length) {
    toggleEdgeError(
      `tapping '${tapped.data("id")}' revealed ${revealed.length} of its ${tapped.connectedEdges('[kind = "depends"]').length} dependency edges`
    );
  }
  const stillHiddenOutside = dependsEdges
    .filter((edge) => tapped.connectedEdges('[kind = "depends"]').filter((mine) => mine.id() === edge.id()).length === 0)
    .every((edge) => edge.hasClass("hidden"));
  if (!stillHiddenOutside) {
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

  // 5. Re-ticking shows everything again.
  toggle.checked = true;
  toggle.fireChange();
  if (dependsEdges.some((edge) => edge.hasClass("hidden"))) {
    toggleEdgeError("re-ticking did not unhide the depends-edges");
  } else {
    report("re-ticked: arrows visible again");
  }
}

if (errors.length) {
  errors.forEach((error) => console.error(`- ${error}`));
  process.exit(1);
}
console.log(
  `OK: ${cy.nodes().length} nodes, ${cy.edges().length} edges ingested; containment, states, ids, cells resolve (${moved} declarations re-spread${fcose ? ", fcose replayed" : ", degraded preset"}; ${dependsEdges.length} toggle-able depends-edges checked)`
);
