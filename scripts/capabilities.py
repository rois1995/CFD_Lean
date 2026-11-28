"""Resolve repository capability evidence without building Lean or consulting GitHub."""
import json
import re
from collections import defaultdict
from pathlib import Path

from verify import CATALOG, CATALOG_STATUS, catalog_index, m1_accepted_theorems

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = "catalog/capabilities.json"
STATUSES = {
    "accepted": "✅ Accepted",
    "implemented": "🟡 Implemented / awaiting acceptance",
    "review": "🧪 Proposal or scientific review",
    "planned": "⬜ Planned",
}
KINDS = {"group", "physics", "geometry", "numerical_method", "certificate", "execution",
         "verification", "architecture"}


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def repo_file(root, path):
    if not isinstance(path, str) or not re.fullmatch(r"[\w./-]+", path):
        raise ValueError(f"Invalid documentation path: {path!r}")
    if path.startswith("/") or ".." in path.split("/") or not (root / path).is_file():
        raise ValueError(f"Missing repository file: {path}")
    return path


def resolve(entries, evidence, root):
    nodes = {}
    for entry in entries:
        key = entry["id"]
        if not re.fullmatch(r"[a-z][a-z0-9_]*", key) or key in nodes:
            raise ValueError(f"Invalid or duplicate capability ID: {key}")
        label, kind = entry["label"], entry["kind"]
        status = entry.get("status")
        if not label.strip() or kind not in KINDS or (
            status is not None if kind == "group" else status not in STATUSES
        ):
            raise ValueError(f"Invalid capability label, kind or status: {key}")
        docs = [repo_file(root, path) for path in entry.get("docs", [])]
        selectors = entry.get("evidence", {})
        if selectors.keys() - evidence.keys():
            raise ValueError(f"Unknown evidence selector: {key}")
        bindings = []
        for kind_of_evidence, ids in selectors.items():
            if not isinstance(ids, list) or len(ids) != len(set(ids)):
                raise ValueError(f"Invalid evidence list: {key}")
            for evidence_id in ids:
                item = evidence[kind_of_evidence].get(evidence_id)
                if item is None:
                    raise ValueError(f"Unknown {kind_of_evidence} evidence: {evidence_id}")
                bindings.append({"id": evidence_id, "type": kind_of_evidence, **item})
        if status == "accepted" and (
            not bindings or any(item["status"] != "accepted" for item in bindings)
        ):
            raise ValueError(f"Accepted capability requires accepted evidence: {key}")
        if status in {"review", "implemented"} and not (bindings or docs):
            raise ValueError(f"Evidence or documentation required: {key}")
        nodes[key] = {**entry, "docs": docs, "evidence": bindings}
    if sum(node["parent"] is None for node in nodes.values()) != 1:
        raise ValueError("Expected one capability root")
    for key, node in nodes.items():
        seen = {key}
        parent = node["parent"]
        while parent is not None:
            if parent not in nodes:
                raise ValueError(f"Missing parent: {parent}")
            if parent in seen:
                raise ValueError(f"Parent cycle at {parent}")
            seen.add(parent)
            parent = nodes[parent]["parent"]
    return list(nodes.values())


def load(root=ROOT):
    result_maps = defaultdict(dict)
    controls = {}
    for path in sorted((root / "specifications").rglob("*-results.json")):
        record = read_json(path)
        if "bindings" in record:
            bindings = {binding["theorem"]: ("", key) for key, binding in record["bindings"].items()}
        else:
            bindings = catalog_index("", record)
            for result in record["results"]:
                if not result.get("declarations") and result.get("controls"):
                    controls[result["id"]] = {
                        "status": "control",
                        "paths": [path.relative_to(root).as_posix()],
                        "controls": result["controls"],
                    }
        for name, (_, result_id) in bindings.items():
            if name in result_maps[result_id]:
                raise ValueError(f"Duplicate result binding: {result_id} / {name}")
            result_maps[result_id][name] = path.relative_to(root).as_posix()
    m1 = m1_accepted_theorems((root / "Integrity.lean").read_text(encoding="utf-8"))
    by_milestone, by_result = defaultdict(list), defaultdict(list)
    seen = set()
    for row in read_json(root / CATALOG)["theorems"]:
        name, result_id, milestone = row["name"], row["id"], row["milestone"]
        if name in seen:
            raise ValueError(f"Duplicate catalog theorem: {name}")
        seen.add(name)
        path = ("specifications/M1.md" if milestone == "M1" and name in m1 else
                result_maps.get(result_id, {}).get(name))
        by_milestone[milestone].append((row, path))
        by_result[result_id].append((row, path))

    def summarize(rows):
        # A partially cataloged binding cannot be promoted through a narrower result ID.
        statuses = {row["status"] for row, _ in rows}
        if any(row["status"] != CATALOG_STATUS.get(row["milestone"]) for row, _ in rows):
            raise ValueError("Catalog status differs from the verifier's acceptance record")
        paths = {repo_file(root, path) for _, path in rows}
        for row, _ in rows:
            repo_file(root, row["module"].replace(".", "/") + ".lean")
        return {"status": next(iter(statuses)) if len(statuses) == 1 else "mixed", "paths": sorted(paths)}

    entries = read_json(root / REGISTRY)["capabilities"]
    indices = {"milestones": by_milestone, "result_ids": by_result}
    evidence = {"milestones": {}, "result_ids": {}}
    for entry in entries:
        for key in entry.get("evidence", {}).get("result_ids", []):
            if key in controls:
                control = controls[key]
                evidence["result_ids"][key] = {
                    "status": control["status"],
                    "paths": control["paths"] + [repo_file(root, path) for path in control["controls"]],
                }
    for entry in entries:
        for kind, index in indices.items():
            for key in entry.get("evidence", {}).get(kind, []):
                if key in index:
                    rows = index[key]
                    current = defaultdict(set)
                    for row, _ in rows:
                        current[row["id"]].add(row["name"])
                    for result_id, names in current.items():
                        expected = set(result_maps.get(result_id, {}))
                        if expected and names != expected:
                            raise ValueError(f"Catalog coverage differs from result map: {result_id}")
                    evidence[kind][key] = summarize(rows)
    return resolve(entries, evidence, root)


if __name__ == "__main__":
    try:
        load()
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit(f"Capability validation failed: {error}")
