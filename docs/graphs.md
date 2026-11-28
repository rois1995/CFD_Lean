# Interactive graphs

Explore the capability hierarchy or follow Lean imports. Import arrows point from the importer to its dependency. Select a node to inspect its evidence or see its direct neighbors.

<section class="graph-viewer" data-graph-viewer data-source-base="__CFDLEAN_SOURCE_BASE__" data-graph-data="../generated/">
  <div class="graph-controls">
    <label>Graph
      <select data-view>
        <option value="layers">Architecture layers</option>
        <option value="modules">Lean modules</option>
        <option value="capabilities">Capabilities</option>
      </select>
    </label>
    <label><span data-filter-label>Layer</span>
      <select data-filter></select>
    </label>
    <form data-search role="search">
      <label>Find a node <input type="search" placeholder="Name or ID" required></label>
      <button type="submit">Find</button>
    </form>
    <button type="button" data-fit>Fit / reset</button>
    <button type="button" data-zoom="out" aria-label="Zoom out">−</button>
    <button type="button" data-zoom="in" aria-label="Zoom in">+</button>
  </div>
  <p data-message role="status">Loading graph…</p>
  <div class="graph-layout">
    <div class="graph-canvas" data-canvas aria-label="Graph canvas"></div>
    <section class="graph-details" data-details aria-label="Node details">
      <p>Select a node or use the search to see its details.</p>
    </section>
  </div>
  <noscript>The interactive viewer requires JavaScript. Use the links below for static diagrams and downloads.</noscript>
</section>

Use the [capability map](CAPABILITIES.md) and [architecture graph](ARCHITECTURE-GRAPH.md) for static diagrams, evidence and GraphML/DOT downloads.
