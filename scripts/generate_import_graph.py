"""Generate the architecture page and module-level Lean import exports."""
import re

from graph_docs import GENERATED, NOTICE, ROOT, export_links, exports, json_text, mermaid, run

MATHEMATICAL = ("Foundations", "Physics", "Geometry", "Discrete", "Entropy", "Schemes", "Time")
LAYERS = (*MATHEMATICAL, "Exec", "Papers", "Verification")
SOURCE_DIRS = ("CFDLean", "Challenges", "benchmarks", "scripts")
TOKEN = re.compile(r"--|/-|-/|(?:[\w'₀-₉]+|«[^»]+»)(?:\.(?:[\w'₀-₉]+|«[^»]+»))*|[^\s]")


def imports(source):
    """Read the Lean module header, including nested comments and import modifiers."""
    def header_tokens():
        depth = 0
        position = 0
        while match := TOKEN.search(source, position):
            token = match[0]
            position = match.end()
            if token == "/-":
                depth += 1
            elif token == "-/" and depth:
                depth -= 1
            elif not depth:
                if token == "--":
                    end = source.find("\n", position)
                    position = len(source) if end == -1 else end + 1
                else:
                    yield token
        if depth:
            raise ValueError("Unterminated block comment in Lean module header")

    tokens = header_tokens()
    token = next(tokens, None)
    for optional in ("module", "prelude"):
        if token == optional:
            token = next(tokens, None)
    while token is not None:
        for optional in ("public", "meta"):
            if token == optional:
                token = next(tokens, None)
        if token != "import":
            return
        name = next(tokens, None)
        if name == "all":
            name = next(tokens, None)
        if name is None or not re.match(r"[\w«]", name):
            raise ValueError("Missing Lean import module")
        yield name.replace("«", "").replace("»", "")
        token = next(tokens, None)


def layer(path):
    if path.parts[0] == "CFDLean":
        return path.parts[1] if len(path.parts) > 2 else "Library"
    return {
        "CFDLean.lean": "Library", "Challenges": "Verification", "benchmarks": "Benchmarks",
        "scripts": "Tooling", "Integrity.lean": "Verification", "KernelAudit.lean": "Verification",
        "StatementChecks.lean": "Verification",
    }.get(path.parts[0], "Entry points")


def graph(root=ROOT):
    paths = sorted([*root.glob("*.lean"),
                    *(path for directory in SOURCE_DIRS for path in (root / directory).rglob("*.lean"))])
    nodes, dependencies = {}, {}
    for path in paths:
        relative = path.relative_to(root)
        module = ".".join(relative.with_suffix("").parts)
        nodes[module] = {"id": module, "label": module, "module": module,
                         "layer": layer(relative), "path": relative.as_posix()}
        dependencies[module] = sorted(set(imports(path.read_text(encoding="utf-8"))))
    edges = []
    for source, targets in dependencies.items():
        for target in targets:
            if target not in nodes:
                if target == "CFDLean" or target.startswith("CFDLean."):
                    raise ValueError(f"{source}: missing repository import {target}")
                continue
            source_layer, target_layer = nodes[source]["layer"], nodes[target]["layer"]
            if source_layer in MATHEMATICAL and target_layer == "Exec":
                raise ValueError(f"Forbidden import: {source} ({source_layer}) -> {target} (Exec)")
            edges.append({"source": source, "target": target, "kind": "import",
                          "source_layer": source_layer, "target_layer": target_layer})
    return {"nodes": list(nodes.values()), "edges": edges}


def layer_graph(data):
    live = {node["layer"] for node in data["nodes"]}
    ordered = [name for name in LAYERS if name in live] + sorted(live - set(LAYERS))
    counts = {}
    for edge in data["edges"]:
        source, target = edge["source_layer"], edge["target_layer"]
        if source != target:
            counts[source, target] = counts.get((source, target), 0) + 1
    return {
        "nodes": [{"id": name, "label": name, "layer": name} for name in ordered],
        "edges": [{"source": source, "target": target, "kind": "import", "count": count}
                  for (source, target), count in sorted(counts.items())],
    }


def markdown(data, layers, diagram):
    lines = [NOTICE.format(generator="python3 scripts/generate_import_graph.py"),
             "# CFD_Lean architecture graph", "",
             "An arrow points from the importing layer to the layer it depends on. "
             "Layer edges summarize direct imports between distinct layers.", "",
             f'The module graph contains {len(data["nodes"])} modules and {len(data["edges"])} direct imports '
             "from the library, entry points, verification, benchmarks and tooling. "
             "The generator checks that the mathematical layers have no direct imports from Exec.", "",
             "[Architecture guide](../ARCHITECTURE.md) · " + export_links("imports") +
             " · [Layer data](generated/imports.json) · [Mermaid source](generated/imports.mmd)", "",
             "```mermaid", diagram.rstrip(), "```", "",
             "## Imports between layers", "",
             "| Importing layer | Imported layer | Direct module imports |", "| --- | --- | ---: |"]
    lines.extend(f'| {edge["source"]} | {edge["target"]} | {edge["count"]} |' for edge in layers["edges"])
    return "\n".join([*lines, ""])


def generate():
    """Generate the import page, layer view and detailed portable exports."""
    data = graph()
    layers = layer_graph(data)
    diagram = mermaid(layers)
    return {
        "docs/ARCHITECTURE-GRAPH.md": markdown(data, layers, diagram),
        f"{GENERATED}/imports.json": json_text(layers),
        f"{GENERATED}/imports.mmd": diagram,
        **exports("imports", data),
    }


if __name__ == "__main__":
    run(generate)
