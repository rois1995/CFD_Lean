"use strict";

const diagrams = document.querySelectorAll("pre.cfd-mermaid");
if (diagrams.length) {
  const library = document.createElement("script");
  library.src = "https://cdn.jsdelivr.net/npm/mermaid@11.12.1/dist/mermaid.min.js";
  library.integrity = "sha384-LlKSgo4Eo5GuF/ZrstLti44dE+GC5XAJ7TSu0Nw9Q3vIZF2QMnkRcK7BUoLabYLF";
  library.crossOrigin = "anonymous";
  library.onload = async () => {
    mermaid.initialize({ startOnLoad: false, securityLevel: "strict", theme: "neutral" });
    for (const [index, source] of [...diagrams].entries()) {
      try {
        const text = (source.querySelector("code") || source).textContent;
        const { svg } = await mermaid.render(`cfd-diagram-${index}`, text);
        const figure = document.createElement("figure");
        figure.innerHTML = svg;
        source.replaceWith(figure);
      } catch (error) {
        console.error("Could not render Mermaid diagram", error);
      }
    }
  };
  document.head.append(library);
}
