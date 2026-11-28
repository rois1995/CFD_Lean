"use strict";

const viewer = document.querySelector("[data-graph-viewer]");
if (viewer) {
  loadCytoscape().then(() => startViewer(viewer)).catch(error => {
    viewer.querySelector("[data-message]").textContent = error.message;
  });
}

function loadCytoscape() {
  return new Promise((resolve, reject) => {
    const script = document.createElement("script");
    script.src = "https://cdn.jsdelivr.net/npm/cytoscape@3.33.1/dist/cytoscape.min.js";
    script.integrity = "sha384-lXrzMjLDk3q9l0I/kjqjMcDgfFnHvWTDeWP3DmMqoeOq49/qa8drmlP3OBWN9dQ3";
    script.crossOrigin = "anonymous";
    script.onload = resolve;
    script.onerror = () => reject(new Error("Could not load the graph library. Static graphs and downloads are linked below."));
    document.head.append(script);
  });
}

async function startViewer(root) {
  const element = name => root.querySelector(`[data-${name}]`);
  const mode = element("view");
  const filter = element("filter");
  const search = element("search");
  const message = element("message");
  const details = element("details");
  const statusLabels = {
    accepted: "Accepted",
    implemented: "Implemented / awaiting acceptance",
    review: "Proposal or scientific review",
    planned: "Planned"
  };
  const dataPaths = {
    layers: "imports.json",
    modules: "graphs/imports.json",
    capabilities: "graphs/capabilities.json"
  };
  const graph = cytoscape({
    container: element("canvas"),
    minZoom: 0.08,
    maxZoom: 4,
    style: [
      { selector: "node", style: {
        "background-color": "#326385", "label": "data(caption)", "font-size": 10,
        "text-wrap": "wrap", "text-max-width": 136, "text-margin-y": -4,
        "color": "#152d3e", "text-outline-width": 2, "text-outline-color": "#f4f8fb",
        "width": 12, "height": 12
      } },
      { selector: "node[status = 'accepted']", style: { "background-color": "#167154" } },
      { selector: "node[status = 'implemented']", style: { "background-color": "#a35b09" } },
      { selector: "node[status = 'review']", style: { "background-color": "#7447a1" } },
      { selector: "node[status = 'planned']", style: { "background-color": "#6b7178" } },
      { selector: "edge", style: {
        "curve-style": "bezier", "line-color": "#8199aa", "target-arrow-color": "#8199aa",
        "target-arrow-shape": "triangle", "arrow-scale": 0.8, "width": 1
      } },
      { selector: ".dim", style: { "opacity": 0.17 } },
      { selector: ".focused", style: { "background-color": "#143148", "width": 19, "height": 19 } }
    ]
  });

  let data;
  let request = 0;
  const cache = new Map();

  function add(parent, tag, text) {
    const child = document.createElement(tag);
    child.textContent = text;
    parent.append(child);
    return child;
  }

  function fileLink(parent, path, label = path) {
    const link = add(parent, "a", label);
    const base = root.dataset.sourceBase;
    const encoded = path.split("/").map(encodeURIComponent).join("/");
    link.href = base === "__CFDLEAN_SOURCE_BASE__" ? `../${encoded}` : base + encoded;
  }

  function clearFocus() {
    graph.elements().removeClass("dim focused");
    details.replaceChildren();
    add(details, "p", "Select a node or use the search to see its details.");
  }

  function select(node) {
    clearFocus();
    graph.elements().difference(node.closedNeighborhood()).addClass("dim");
    node.addClass("focused");
    const item = node.data();
    details.replaceChildren();
    add(details, "h2", item.label);
    if (item.status) add(details, "p", statusLabels[item.status]);
    if (item.layer) add(details, "p", item.layer);
    if (item.kind && item.kind !== "group") add(details, "p", item.kind.replaceAll("_", " "));
    const paths = new Map();
    if (item.path) paths.set(item.path, item.path);
    for (const path of item.docs || []) paths.set(path, path);
    for (const evidence of item.evidence || []) {
      for (const path of evidence.paths) {
        paths.set(path, paths.has(path) ? `${paths.get(path)}, ${evidence.id}` : evidence.id);
      }
    }
    if (paths.size) {
      add(details, "h3", "Evidence and source");
      const list = add(details, "ul", "");
      for (const [path, label] of paths) fileLink(add(list, "li", ""), path, label);
    }
    for (const [title, neighbors] of [["Incoming", node.incomers().nodes()], ["Outgoing", node.outgoers().nodes()]]) {
      if (neighbors.empty()) continue;
      add(details, "h3", title);
      const list = add(details, "ul", "");
      for (const neighbor of neighbors) {
        const button = add(add(list, "li", ""), "button", neighbor.data("label"));
        button.type = "button";
        button.addEventListener("click", () => {
          select(neighbor);
          graph.center(neighbor);
        });
      }
    }
  }

  function render() {
    clearFocus();
    const selected = filter.value;
    const key = mode.value === "capabilities" ? "status" : "layer";
    const nodes = data.nodes.filter(node => !selected || node[key] === selected || node.kind === "group");
    const ids = new Set(nodes.map(node => node.id));
    const edges = data.edges.filter(edge => ids.has(edge.source) && ids.has(edge.target));
    graph.batch(() => {
      graph.elements().remove();
      graph.add(nodes.map(node => ({ data: {
        ...node,
        caption: node.module ? node.module.split(".").slice(-2).join(".") : node.label
      } })));
      graph.add(edges.map((edge, id) => ({ data: { ...edge, id: `edge-${id}` } })));
    });
    const layout = mode.value === "capabilities" ? "breadthfirst" : "cose";
    graph.layout({ name: layout, directed: true, animate: false, randomize: true, padding: 28 }).run();
    message.textContent = `${nodes.length} nodes · ${edges.length} connections`;
  }

  async function changeView() {
    const current = ++request;
    const view = mode.value;
    data = undefined;
    graph.elements().remove();
    clearFocus();
    filter.replaceChildren();
    filter.disabled = true;
    message.textContent = "Loading graph…";
    try {
      if (!cache.has(view)) {
        const response = await fetch(new URL(root.dataset.graphData + dataPaths[view], location.href));
        if (!response.ok) throw new Error(`HTTP ${response.status}`);
        cache.set(view, await response.json());
      }
      if (current !== request) return;
      data = cache.get(view);
      const capabilities = view === "capabilities";
      element("filter-label").textContent = capabilities ? "Status" : "Layer";
      filter.add(new Option(capabilities ? "All statuses" : "All layers", ""));
      const values = capabilities ? Object.keys(statusLabels) : [...new Set(data.nodes.map(node => node.layer))].sort();
      for (const value of values) filter.add(new Option(statusLabels[value] || value, value));
      if (view === "modules" && values.includes("Foundations")) filter.value = "Foundations";
      filter.disabled = false;
      render();
    } catch (error) {
      if (current === request) message.textContent = `Could not load graph data (${error.message}).`;
    }
  }

  mode.addEventListener("change", changeView);
  filter.addEventListener("change", () => data && render());
  graph.on("tap", "node", event => select(event.target));
  graph.on("tap", event => { if (event.target === graph) clearFocus(); });
  element("fit").addEventListener("click", () => {
    clearFocus();
    graph.fit(undefined, 28);
  });
  for (const button of root.querySelectorAll("[data-zoom]")) {
    button.addEventListener("click", () => {
      graph.zoom({ level: graph.zoom() * (button.dataset.zoom === "in" ? 1.25 : 0.8),
        renderedPosition: { x: graph.width() / 2, y: graph.height() / 2 } });
    });
  }
  search.addEventListener("submit", event => {
    event.preventDefault();
    const query = search.querySelector("input").value.trim().toLowerCase();
    if (!data || !query) return;
    const matches = data.nodes.filter(node => [node.label, node.id].some(value => value.toLowerCase().includes(query)));
    const match = matches.find(node => [node.id, node.label].some(value => value.toLowerCase() === query)) ||
      matches.find(node => !graph.getElementById(node.id).empty()) || matches[0];
    if (!match) {
      message.textContent = "No matching nodes.";
      return;
    }
    if (graph.getElementById(match.id).empty()) {
      filter.value = mode.value === "capabilities" ? match.status || "" : match.layer;
      render();
    }
    const node = graph.getElementById(match.id);
    select(node);
    graph.zoom(Math.max(graph.zoom(), 0.9));
    graph.center(node);
    message.textContent = `${matches.length} match${matches.length === 1 ? "" : "es"} · ${match.label}`;
  });
  await changeView();
}
