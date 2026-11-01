/**
 * Runtime harness for axbt's generated graph page.
 *
 * Usage: node graph_runtime_harness.js <graph.html> <cytoscape.min.js>
 *
 * Runs the page's own application script with a minimal DOM stub, then
 * replays the captured construction options through a REAL Cytoscape
 * (headless — no container) and asserts the element parse the browser
 * would perform: every node/edge ingests, containment resolves, states
 * arrive as classes. Catches the "renders a legend but no data" class
 * of bug that text assertions cannot see.
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
const jsMatch = page.match(/<script>\n([\s\S]*?)\n<\/script>\n<\/body>/);
if (!docMatch || !jsMatch) {
  console.error("page missing the data block or application script");
  process.exit(2);
}

// The stub `cy` captures the construction options; the script's later
// imperative calls (fit, on) become no-ops.
let captured = null;
const documentStub = {
  getElementById(id) {
    if (id === "graph-data") {
      return { id, textContent: docMatch[1] };
    }
    return { id, style: {} };
  },
};
const harnessWindow = {
  cytoscape(options) {
    captured = options;
    return { fit() {}, on() {} };
  },
};

const script = jsMatch[1];
try {
  new Function("window", "document", script)(harnessWindow, documentStub);
} catch (error) {
  console.error("page script threw:", error);
  process.exit(2);
}
if (!captured) {
  console.error("page script never constructed a Cytoscape instance");
  process.exit(2);
}

// Replay the captured options through the real Cytoscape, headless.
let cy;
try {
  cy = cytoscape(Object.assign(headlessOptions(captured), { headless: true }));
} catch (error) {
  console.error("real Cytoscape rejected the captured options:", error);
  process.exit(2);
}

const payload = JSON.parse(docMatch[1]);
const errors = [];
const nodeCount = cy.nodes().length;
const edgeCount = cy.edges().length;
if (nodeCount !== payload.nodes.length) {
  errors.push(`expected ${payload.nodes.length} nodes, real Cytoscape ingested ${nodeCount}`);
}
if (edgeCount !== payload.edges.length) {
  errors.push(`expected ${payload.edges.length} edges, real Cytoscape ingested ${edgeCount}`);
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
if (stateSum !== nodeCount) {
  errors.push(`state classes cover ${stateSum} of ${nodeCount} nodes`);
}
// Id lookup and edge connectivity work the way the page's handlers do.
for (const element of payload.nodes.concat(payload.edges)) {
  if (cy.getElementById(element.id).length === 0) {
    errors.push(`element not ingested: ${element.id}`);
  }
}
// Edge-connected elements highlight their neighborhoods (compound
// containment is NOT an edge, so isolated declarations are exactly
// one element — the click handler highlights what exists).
const edgeSource = payload.edges[0]
  ? cy.getElementById(payload.edges[0].source)
  : null;
if (edgeSource && edgeSource.closedNeighborhood().size() < 2) {
  errors.push("closedNeighborhood of an edge source has < 2 elements");
}

if (errors.length) {
  errors.forEach((error) => console.error(`- ${error}`));
  process.exit(1);
}
console.log(
  `OK: ${nodeCount} nodes, ${edgeCount} edges ingested; containment, states, and ids resolve`
);

function headlessOptions(options) {
  const clone = Object.assign({}, options);
  delete clone.container;
  clone.elements = options.elements; // keep exactly what the page built
  return clone;
}
