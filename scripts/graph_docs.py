"""Emit consistent, deterministic documentation and portable graph formats."""
import argparse
import json
from pathlib import Path
import sys
from xml.etree import ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
GENERATED = "docs/generated"
NOTICE = "<!-- Generated file. Edit its sources and rerun {generator}. -->"
EXPORTS = ("graphml", "dot", "json")


def json_text(data):
    return json.dumps(data, ensure_ascii=False, indent=2) + "\n"


def attribute(value):
    return value if isinstance(value, str) else json.dumps(value, ensure_ascii=False, sort_keys=True)


def graphml(graph):
    root = ET.Element("graphml", xmlns="http://graphml.graphdrawing.org/xmlns")
    attributes = {}
    for tag, items, identifiers in (("node", graph["nodes"], {"id"}),
                                    ("edge", graph["edges"], {"source", "target"})):
        attributes[tag] = sorted(set().union(*(item.keys() for item in items)) - identifiers)
        for key in attributes[tag]:
            ET.SubElement(root, "key", id=f"{tag}_{key}",
                          attrib={"for": tag, "attr.name": key, "attr.type": "string"})
    body = ET.SubElement(root, "graph", id="graph", edgedefault="directed")
    for item in graph["nodes"]:
        node = ET.SubElement(body, "node", id=item["id"])
        for key in attributes["node"]:
            if key in item and item[key] is not None:
                ET.SubElement(node, "data", key=f"node_{key}").text = attribute(item[key])
    for item in graph["edges"]:
        edge = ET.SubElement(body, "edge", source=item["source"], target=item["target"])
        for key in attributes["edge"]:
            if key in item:
                ET.SubElement(edge, "data", key=f"edge_{key}").text = attribute(item[key])
    ET.indent(root)
    return ET.tostring(root, encoding="unicode", xml_declaration=True) + "\n"


def dot(graph):
    def quote(text):
        return json.dumps(text, ensure_ascii=False)

    def attrs(item, excluded):
        return ", ".join(f"{key}={quote(attribute(value))}" for key, value in sorted(item.items())
                         if key not in excluded and value is not None)

    lines = ["digraph {"]
    for node in graph["nodes"]:
        lines.append(f'  {quote(node["id"])} [{attrs(node, {"id"})}];')
    for edge in graph["edges"]:
        lines.append(f'  {quote(edge["source"])} -> {quote(edge["target"])} '
                     f'[{attrs(edge, {"source", "target"})}];')
    return "\n".join([*lines, "}", ""])


def exports(name, graph):
    return {f"{GENERATED}/graphs/{name}.{ext}": render(graph)
            for ext, render in (("graphml", graphml), ("dot", dot), ("json", json_text))}


def mermaid(graph, label=lambda node: node["label"]):
    ids = {node["id"]: f"n_{index}" for index, node in enumerate(graph["nodes"])}
    lines = ["flowchart TD"]
    escapes = str.maketrans({character: f"#{ord(character)};" for character in '#<>&"[]'})
    for node in graph["nodes"]:
        lines.append(f'    {ids[node["id"]]}["{label(node).translate(escapes)}"]')
    for edge in graph["edges"]:
        lines.append(f'    {ids[edge["source"]]} --> {ids[edge["target"]]}')
    return "\n".join([*lines, ""])


def export_links(name):
    return " · ".join(f"[{ext.upper()}](generated/graphs/{name}.{ext})" for ext in EXPORTS)


def write_outputs(outputs, check, root=ROOT):
    stale = []
    for relative, content in outputs.items():
        path = root / relative
        data = content.encode("utf-8")
        if check:
            if not path.is_file() or path.read_bytes() != data:
                stale.append(relative)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    return stale


def run(generate):
    parser = argparse.ArgumentParser(description=generate.__doc__)
    parser.add_argument("--check", action="store_true", help="Report stale output without writing files.")
    args = parser.parse_args()
    try:
        stale = write_outputs(generate(), args.check)
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(1, f"Generation failed: {error}\n")
    if stale:
        print("Stale generated files:\n" + "\n".join(stale), file=sys.stderr)
        parser.exit(1, f"Regenerate with python3 {sys.argv[0]}.\n")
