"""Generate the capability page and its Mermaid, JSON, GraphML and DOT representations."""
from capabilities import CATALOG, REGISTRY, STATUSES, load
from graph_docs import GENERATED, NOTICE, export_links, exports, json_text, mermaid, run


def graph():
    nodes = load()
    return {
        "generated_from": {"capability_registry": REGISTRY, "theorem_catalog": CATALOG},
        "nodes": nodes,
        "edges": [{"source": node["parent"], "target": node["id"], "kind": "contains"}
                  for node in nodes if node["parent"] is not None],
    }


def diagram(data):
    def label(node):
        return f'{STATUSES[node["status"]].split()[0]} {node["label"]}' if node.get("status") else node["label"]

    return mermaid(data, label)


def markdown(data):
    categories = [node for node in data["nodes"] if node["kind"] == "group"]
    ids = {node["id"] for node in categories}
    edges = [edge for edge in data["edges"] if edge["target"] in ids and edge["source"] in ids]
    lines = [NOTICE.format(generator="`python3 scripts/generate_capabilities.py`"),
             "# CFD_Lean capabilities", "",
             "The registry records the status of each capability at the checked-out revision. "
             "Acceptance applies to the linked results and their stated hypotheses. "
             "Exact-real refinement and native arithmetic have separate evidence.", "",
             " · ".join(STATUSES.values()), "", export_links("capabilities"),
             " · [Full Mermaid source](generated/capabilities.mmd)", "",
             "```mermaid", diagram({"nodes": categories, "edges": edges}).rstrip(), "```", "",
             "## Capability evidence", "",
             "| Capability | Status | Evidence and documentation |", "| --- | --- | --- |"]
    for node in data["nodes"]:
        status = node.get("status")
        if status is None:
            continue
        evidence = [f'[{item["id"]}](../{item["paths"][0]})' for item in node["evidence"]]
        evidence.extend(f"[{path.rsplit('/', 1)[-1]}](../{path})" for path in node["docs"])
        label = node["label"].replace("|", "\\|")
        lines.append(f'| {label} | {STATUSES[status]} | {", ".join(evidence) or "—"} |')
    lines.extend(["", "## Next architectural steps", ""])
    lines.extend(f'- {node["label"]}' for node in data["nodes"] if node.get("status") == "planned")
    return "\n".join([*lines, ""])


def generate():
    """Generate the capability page and its portable graph exports."""
    data = graph()
    return {
        "docs/CAPABILITIES.md": markdown(data),
        f"{GENERATED}/capabilities.mmd": diagram(data),
        f"{GENERATED}/capabilities.json": json_text(data),
        **exports("capabilities", data),
    }


if __name__ == "__main__":
    run(generate)
