"""Build, inventory elaborated mathematical declarations, and verify the frozen contracts."""
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
M4_ACCEPTED_REVISION = "3a586a42546cba1784cc79269e3f9d1c5d843f0c"
M4A_ACCEPTED_REVISION = "37c1e6ee4618b0183135c2795b3aa6ebea2f22d5"
ACCEPTED_BASELINE = M4_ACCEPTED_REVISION
M3_ACCEPTED_REVISION = "e2ea538b8da38c01c098ef28a3ea31030d90c6bb"
M2_ACCEPTED_REVISION = "ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1"
APPROVED_M5 = "9ee58a9a0226844cda835ac0b8285d64891f1dd0"
APPROVED_M4 = "0cff4af244b85f4e2071e7bf941d40fdd0a399b5"
APPROVED_M3 = "3189a603b3f6af953f0828d6b2e239320fd2cd20"
APPROVED_M2 = "79fd2a03d7b15325c56a88ec83991b4fb4f498bb"
# MC-T: reviewed toolchain port (Lean v4.19.0 -> v4.36.0). Accepted sources may differ from their accepted
# revision only by being byte-identical to this port revision; accepted types may differ only as recorded in
# specifications/MC-port-types.json with a mechanical classification.
MC_PORT_REVISION = "4f249ae108bc71f069427d09275ddc29cf1f0f7a"
MC_PORT_CLASSES = {"notation", "mathlib-rename", "pretty-printer"}
MC_PORT_MAP = "specifications/MC-port-types.json"
MC_PORT_MAP_SHA256 = "e333f9a76687ea7ca34e6b60b86bcb096b2e4696124393a7e439c4c91365dc8c"
MC_PORT_COUNT = 199
_PORT_MAP = None
# MC-N: numerical core library (namespace CFDLean.Num) moved from JST_Paper_Lean. The check is additive: every
# promised MC-N theorem is a kernel-checked root theorem with standard axioms in its CFDLean.Num module, and no
# pre-existing CFDLean source (M1-M5) differs from the MC-N base revision.
MC_N_RESULTS = "specifications/MC-N-results.json"
MC_N_BASE_REVISION = "497b356610429c0760597724551b746605e038ba"
MC_N_COUNT = 37
MC_N_MODULES = {"CFDLean.Num." + name for name in
                ["Basic", "LogMean", "Simplex", "Mesh", "Boundary", "PairFlux", "Galerkin", "Production", "Bridge"]}


def load_port_map(data):
    if hashlib.sha256(data).hexdigest() != MC_PORT_MAP_SHA256:
        raise ValueError("MC port map differs from the reviewed map")
    record = json.loads(data)
    if record["count"] != MC_PORT_COUNT or len(record["theorems"]) != MC_PORT_COUNT:
        raise ValueError("MC port map does not cover the reviewed promised theorems")
    for name, entry in record["theorems"].items():
        same = entry["accepted_type"] == entry["current_type"]
        if (entry["classification"] == "identical") != same or (
                not same and entry["classification"] not in MC_PORT_CLASSES):
            raise ValueError(f"MC port map entry inconsistent with its class: {name}")
    return record["theorems"]


def port_map():
    global _PORT_MAP
    if _PORT_MAP is None:
        _PORT_MAP = load_port_map((ROOT / MC_PORT_MAP).read_bytes())
    return _PORT_MAP


def same_or_ported_type(name, before, after, mapping=None):
    if before == after:
        return True
    entry = (port_map() if mapping is None else mapping).get(name)
    return (entry is not None and entry["classification"] in MC_PORT_CLASSES
            and entry["accepted_type"] == before and entry["current_type"] == after)


def same_or_ported_source(path, accepted_sha256):
    data = (ROOT / path).read_bytes()
    if hashlib.sha256(data).hexdigest() == accepted_sha256:
        return True
    try:
        return data == git_blob(MC_PORT_REVISION, path)
    except subprocess.CalledProcessError:
        return False


def parse_axioms(output):
    rows = {}
    for line in output.splitlines():
        if "CFDLEAN_DECL " not in line:
            continue
        row = json.loads(line.split("CFDLEAN_DECL ", 1)[1])
        name = row["name"]
        if name in rows:
            raise ValueError(f"Duplicate qualified audit record: {name}")
        if row["root"] and (row["unsafe"] or set(row["axioms"]) - ALLOWED):
            raise ValueError(f"Forbidden dependency in {name}")
        rows[name] = row
    if not rows:
        raise ValueError("Empty elaborated declaration inventory")
    return rows


def check_result_ids(contract, text, milestone="M2"):
    approved = re.findall(r"^\| (" + re.escape(milestone) + r"-[A-Z]+[0-9]*) \|", text, re.MULTILINE)
    bound = [result["id"] for result in contract["results"]]
    if not approved or len(bound) != len(set(bound)) or set(bound) != set(approved):
        raise ValueError("Result bindings differ from the separately frozen approved list")


def check_promises(rows, contract, stage, stages=("M2a", "M2b", "M2c", "M2d")):
    active = [result for result in contract["results"]
              if stages.index(result["stage"]) <= stages.index(stage)]
    if any(not result["declarations"] for result in active):
        raise ValueError("An active approved result has no declaration binding")
    required = {name for result in active for name in result["declarations"]}
    if not required:
        raise ValueError(f"No approved result bindings for {stage}")
    for name in required:
        if name not in rows or rows[name]["kind"] != "theorem" or not rows[name]["root"]:
            raise ValueError(f"Missing promised theorem: {name}")
    return sorted(required)


def check_inherited(rows, contract, accepted_contract, accepted_evidence):
    stages = ["M2a", "M2b", "M2c", "M2d"]
    active = [r for r in accepted_contract["results"]
              if stages.index(r["stage"]) <= stages.index(accepted_contract["current_stage"])]
    current = {r["id"]: r for r in contract["results"]}
    comparison = {}
    for inherited in active:
        if not inherited["declarations"] or current.get(inherited["id"]) != inherited:
            raise ValueError(f"Accepted {inherited['id']} binding or stage changed")
        for name in inherited["declarations"]:
            before = accepted_evidence["declarations"][name]["type"]
            after = rows[name]["type"]
            comparison[name] = {"accepted_type": before, "current_type": after}
            if not same_or_ported_type(name, before, after):
                raise ValueError(f"Accepted theorem type changed: {name}")
    return comparison



def check_m3_layout(contract, approved):
    for field in ["contract", "contract_sha256", "representation_contract", "representation_sha256",
                  "reviewed_proposal_revision", "approval_record"]:
        if contract.get(field) != approved.get(field):
            raise ValueError("M3 frozen contract metadata changed")
    def layout(value):
        return [(r["id"], [p["stage"] for p in r["parts"]]) for r in value["results"]]
    if layout(contract) != layout(approved):
        raise ValueError("M3 result stages/parts differ from frozen approval")


def check_m4_layout(contract, approved):
    for field in ["contract", "contract_sha256", "precision_contract", "precision_sha256",
                  "reviewed_proposal_revision", "approval_record"]:
        if contract.get(field) != approved.get(field):
            raise ValueError("M4 frozen contract metadata changed")
    layout = lambda value: [(r["id"], r["stage"]) for r in value["results"]]
    if layout(contract) != layout(approved):
        raise ValueError("M4 result IDs/stages differ from frozen approval")


def check_m5_layout(contract, approved):
    for field in ["contract", "contract_sha256", "reviewed_proposal_revision", "approval_record", "current_stage"]:
        if contract.get(field) != approved.get(field):
            raise ValueError("M5 frozen contract metadata changed")
    layout = lambda value: [(r["id"], r["stage"]) for r in value["results"]]
    if layout(contract) != layout(approved):
        raise ValueError("M5 result IDs/stages differ from frozen approval")


def check_m3_inherited(rows, contract, accepted, evidence):
    stages = ("M3a", "M3b")
    current = {(r["id"], p["stage"]): p for r in contract["results"] for p in r["parts"]}
    comparisons = {}
    for result in accepted["results"]:
        for part in result["parts"]:
            if stages.index(part["stage"]) > stages.index(accepted["current_stage"]):
                continue
            if not part["declarations"] or current.get((result["id"], part["stage"])) != part:
                raise ValueError(f"Accepted {result['id']} part/bindings changed")
            for name in part["declarations"]:
                before, after = evidence["declarations"][name]["type"], rows[name]["type"]
                if not same_or_ported_type(name, before, after):
                    raise ValueError(f"Accepted M3 type changed: {name}")
                comparisons[name] = {"accepted_type": before, "current_type": after}
    return comparisons


def check_m4_inherited(rows, contract, accepted, evidence):
    stages = ("M4a", "M4b")
    if stages.index(contract["current_stage"]) < stages.index(accepted["current_stage"]):
        raise ValueError("Accepted M4 current stage rolled back")
    current = {r["id"]: r for r in contract["results"]}
    comparisons = {}
    for result in accepted["results"]:
        if stages.index(result["stage"]) > stages.index(accepted["current_stage"]):
            continue
        if not result["declarations"] or current.get(result["id"]) != result:
            raise ValueError(f"Accepted {result['id']} binding/stage changed")
        for name in result["declarations"]:
            before, after = evidence["declarations"][name]["type"], rows[name]["type"]
            if not same_or_ported_type(name, before, after):
                raise ValueError(f"Accepted M4 type changed: {name}")
            comparisons[name] = {"accepted_type": before, "current_type": after}
    return comparisons


def check_mc_n(rows, record, other_promised, spec_text):
    results = record["results"]
    ids = [r["id"] for r in results]
    names = [r["theorem"] for r in results]
    if (len(results) != MC_N_COUNT or len(set(ids)) != len(ids) or len(set(names)) != len(names)
            or any(not i.startswith("MC-N.") for i in ids)):
        raise ValueError("MC-N result bindings differ from the frozen scope")
    for module in MC_N_MODULES:
        if f"`{module.rsplit('.', 1)[1]}`" not in spec_text:
            raise ValueError(f"MC-N module not in the frozen module list: {module}")
    for result in results:
        name = result["theorem"]
        if result["module"] not in MC_N_MODULES or not name.startswith("CFDLean.Num."):
            raise ValueError(f"MC-N theorem outside the numerical core: {name}")
        row = rows.get(name)
        if (row is None or row["kind"] != "theorem" or not row["root"] or row["unsafe"]
                or set(row["axioms"]) - ALLOWED):
            raise ValueError(f"Missing MC-N theorem: {name}")
        if row["module"] != result["module"]:
            raise ValueError(f"MC-N theorem outside its module: {name}")
    if set(names) & set(other_promised):
        raise ValueError("MC-N rebinds an M1-M5 promised theorem")
    return sorted(names)


def check_mc_n_sources(paths, read, base):
    """Pre-existing CFDLean sources (M1-M5) are byte-identical to the MC-N base; only the umbrella changes."""
    checked = 0
    for path in paths:
        if path == "CFDLean.lean" or path.startswith("CFDLean/Num/") or path == "CFDLean/Num.lean":
            continue
        try:
            before = base(path)
        except subprocess.CalledProcessError:
            continue
        if read(path) != before:
            raise ValueError(f"MC-N changed an M1-M5 source: {path}")
        checked += 1
    if not checked:
        raise ValueError("No M1-M5 source compared with the MC-N base")
    return checked


def git_blob(revision, path):
    return subprocess.check_output(["git", "show", f"{revision}:{path}"])


def main():
    os.chdir(ROOT)
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    contract = json.loads((ROOT / "specifications/M2-results.json").read_text())
    frozen = (ROOT / contract["contract"]).read_bytes()
    digest = hashlib.sha256(frozen).hexdigest()
    if digest != contract["contract_sha256"]:
        raise ValueError("Frozen scientific contract changed; approval amendment required")
    if frozen != git_blob(APPROVED_M2, "specifications/M2.md"):
        raise ValueError("Contract differs from immutable approval revision")
    accepted_contract = json.loads(git_blob(ACCEPTED_BASELINE, "specifications/M2-results.json"))
    accepted_evidence = json.loads(git_blob(ACCEPTED_BASELINE, "evidence/verification.json"))
    for module, record in accepted_evidence["source_modules"].items():
        if module != "CFDLean" and not same_or_ported_source(record["path"], record["sha256"]):
            raise ValueError(f"Accepted mathematical source changed: {record['path']}")
    check_result_ids(contract, frozen.decode())
    for name, expected in contract["accepted_m1_sources"].items():
        if not same_or_ported_source(name, expected):
            raise ValueError(f"Accepted M1 source changed: {name}")
    m3 = json.loads((ROOT / "specifications/M3-results.json").read_text())
    for field, digest_field in [("contract", "contract_sha256"), ("representation_contract", "representation_sha256")]:
        data = (ROOT / m3[field]).read_bytes()
        if hashlib.sha256(data).hexdigest() != m3[digest_field] or data != git_blob(APPROVED_M3, m3[field]):
            raise ValueError("M3 scientific contract differs from frozen approval")
    approved_m3 = json.loads(git_blob(APPROVED_M3, "specifications/M3-results.json"))
    check_m3_layout(m3, approved_m3)
    check_result_ids(m3, (ROOT / m3["contract"]).read_text(), "M3")
    m4 = json.loads((ROOT / "specifications/M4-results.json").read_text())
    for field, digest_field in [("contract", "contract_sha256"), ("precision_contract", "precision_sha256")]:
        data = (ROOT / m4[field]).read_bytes()
        if hashlib.sha256(data).hexdigest() != m4[digest_field] or data != git_blob(APPROVED_M4, m4[field]):
            raise ValueError("M4 scientific contract differs from frozen approval")
    if (ROOT / m4["approval_record"]).read_bytes() != git_blob(APPROVED_M4, m4["approval_record"]):
        raise ValueError("M4 approval record differs from immutable authorization")
    check_m4_layout(m4, json.loads(git_blob(APPROVED_M4, "specifications/M4-results.json")))
    check_result_ids(m4, (ROOT / m4["contract"]).read_text(), "M4")
    m5 = json.loads((ROOT / "specifications/M5-results.json").read_text())
    data = (ROOT / m5["contract"]).read_bytes()
    if hashlib.sha256(data).hexdigest() != m5["contract_sha256"] or data != git_blob(APPROVED_M5, m5["contract"]):
        raise ValueError("M5 scientific contract differs from frozen approval")
    if data != git_blob(m5["reviewed_proposal_revision"], "specifications/M5-proposal.md"):
        raise ValueError("M5 contract differs from the independently reviewed proposal")
    if (ROOT / m5["approval_record"]).read_bytes() != git_blob(APPROVED_M5, m5["approval_record"]):
        raise ValueError("M5 approval record differs from immutable authorization")
    check_m5_layout(m5, json.loads(git_blob(APPROVED_M5, "specifications/M5-results.json")))
    check_result_ids(m5, data.decode(), "M5")
    env = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1", LAKE_NO_CACHE="1")
    with (evidence / "build.log").open("w") as log:
        subprocess.run(["lake", "build"], env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    result = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "KernelAudit.lean"],
                            env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (evidence / "kernel-inventory.log").write_text(result.stdout)
    result.check_returncode()
    rows = parse_axioms(result.stdout)
    modules = [json.loads(line.split("CFDLEAN_MODULES ", 1)[1])
               for line in result.stdout.splitlines() if "CFDLEAN_MODULES " in line]
    closures = [json.loads(line.split("CFDLEAN_CLOSURE ", 1)[1])
                for line in result.stdout.splitlines() if "CFDLEAN_CLOSURE " in line]
    expected_modules = {"CFDLean", "Integrity"} | {
        ".".join(path.relative_to(ROOT).with_suffix("").parts)
        for path in (ROOT / "CFDLean").rglob("*.lean")}
    if len(modules) != 1 or set(modules[0]) != expected_modules or len(closures) != 1:
        raise ValueError("Elaborated module or closure coverage mismatch")
    if closures[0]["unsafe_reached"] or set(closures[0]["axioms"]) - ALLOWED:
        raise ValueError("Forbidden transitive dependency")
    m2_promised = check_promises(rows, contract, contract["current_stage"])
    parts = {"results": [p for r in m3["results"] for p in r["parts"]]}
    m3_promised = check_promises(rows, parts, m3["current_stage"], ("M3a", "M3b"))
    m4_promised = check_promises(rows, m4, m4["current_stage"], ("M4a", "M4b"))
    m5_promised = check_promises(rows, m5, m5["current_stage"], ("M5",))
    promised = sorted(set(m2_promised + m3_promised + m4_promised + m5_promised))
    mcn = json.loads((ROOT / MC_N_RESULTS).read_text())
    mcn_spec = (ROOT / mcn["specification"]).read_bytes()
    if hashlib.sha256(mcn_spec).hexdigest() != mcn["specification_sha256"]:
        raise ValueError("MC-N scope differs from the recorded specification")
    mcn_promised = check_mc_n(rows, mcn, promised, mcn_spec.decode())
    mcn_sources = check_mc_n_sources(
        sorted(str(path.relative_to(ROOT)) for path in (ROOT / "CFDLean").rglob("*.lean")),
        lambda path: (ROOT / path).read_bytes(), lambda path: git_blob(MC_N_BASE_REVISION, path))
    inherited = check_inherited(rows, contract, accepted_contract, accepted_evidence)
    accepted_m3 = json.loads(git_blob(ACCEPTED_BASELINE, "specifications/M3-results.json"))
    inherited.update(check_m3_inherited(rows, m3, accepted_m3, accepted_evidence))
    accepted_m4 = json.loads(git_blob(ACCEPTED_BASELINE, "specifications/M4-results.json"))
    inherited.update(check_m4_inherited(rows, m4, accepted_m4, accepted_evidence))
    (evidence / "inherited-types.json").write_text(json.dumps(inherited, indent=2) + "\n")
    (evidence / "binding-type-diff.json").write_text(json.dumps({name: {
        "accepted_type": accepted_evidence["declarations"][name]["type"]
            if name in accepted_evidence["promised_theorems"] else None,
        "current_type": rows[name]["type"]
    } for name in promised}, indent=2) + "\n")
    (evidence / "bindings-diff.patch").write_bytes(subprocess.check_output(
        ["git", "diff", ACCEPTED_BASELINE, "--", "specifications/M2-results.json", "specifications/M3-results.json", "specifications/M4-results.json", "specifications/M5-results.json"]))
    with (evidence / "statement-checks.log").open("w") as log:
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "StatementChecks.lean"],
                       env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        path = ROOT / ".lake/packages" / package["name"]
        revision = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True)
        if revision != package["rev"] or dirty:
            raise ValueError(f"Dependency revision or tracked source mismatch: {package['name']}")
    files = [ROOT / name for name in [".gitignore", "README.md", "lean-toolchain", "lakefile.toml",
                                     "lake-manifest.json", "CFDLean.lean", "Integrity.lean", "KernelAudit.lean", "StatementChecks.lean"]]
    for directory in ["CFDLean", "references", "specifications", "scripts"]:
        files.extend(path for path in (ROOT / directory).rglob("*")
                     if path.is_file() and "__pycache__" not in path.parts)
    (evidence / "SHA256SUMS").write_text("".join(
        f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT)}\n"
        for path in sorted(files)))
    (evidence / "verification.json").write_text(json.dumps({
        "lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
        "stage": m5["current_stage"], "m4_stage": m4["current_stage"], "m3_stage": m3["current_stage"], "m2_stage": contract["current_stage"], "promised_theorems": promised,
        "modules": sorted(modules[0]), "closure": closures[0],
        "source_modules": {module: {
            "path": module.replace(".", "/") + ".lean",
            "sha256": hashlib.sha256((ROOT / (module.replace(".", "/") + ".lean")).read_bytes()).hexdigest()
        } for module in sorted(modules[0])},
        "declarations": dict(sorted(rows.items())),
        "deferred_result_ids": [r["id"] for r in m4["results"] if
            ("M4a", "M4b").index(r["stage"]) > ("M4a", "M4b").index(m4["current_stage"])],
        "dependency_revisions_checked": len(manifest["packages"]),
        "m1_acceptance_record": "reviews/M1/CFD_Lean_M1_Acceptance.md",
        "m2a_acceptance_record": "reviews/M2a/Acceptance.md",
        "m2b_acceptance_record": "reviews/M2b/Acceptance.md",
        "m2c_acceptance_record": "reviews/M2c/Acceptance.md",
        "accepted_inherited_revision": ACCEPTED_BASELINE, "inherited_types_checked": len(inherited),
        "m2_approval_record": contract["approval_record"], "m2_independent_acceptance": "accepted at " + M2_ACCEPTED_REVISION,
        "m2_acceptance_record": "reviews/M2/Acceptance.md", "m3_approval_record": m3["approval_record"],
        "m3a_acceptance_record": "reviews/M3a/Acceptance.md",
        "m3b_acceptance_record": "reviews/M3b/Acceptance.md",
        "m3_acceptance_record": "reviews/M3/Acceptance.md",
        "m3_independent_acceptance": "accepted at " + M3_ACCEPTED_REVISION,
        "m4_approval_record": m4["approval_record"], "m4a_acceptance_record": "reviews/M4a/Acceptance.md",
        "m4b_acceptance_record": "reviews/M4b/Acceptance.md",
        "m4_acceptance_record": "reviews/M4/Acceptance.md",
        "m4_independent_acceptance": "accepted at " + M4_ACCEPTED_REVISION,
        "m5_approval_record": m5["approval_record"],
        "m5_proposal_review": "reviews/M5/proposal-3dcb73d/report/Review_Record.json",
        "m5_independent_acceptance": "pending implementation review",
        "mc_n_results": MC_N_RESULTS, "mc_n_promised_theorems": mcn_promised,
        "mc_n_base_revision": MC_N_BASE_REVISION, "mc_n_unchanged_sources": mcn_sources
    }, indent=2) + "\n")
    print(f"Verified {len(rows)} qualified inventory records, {len(promised)} promised theorems, "
          f"{len(mcn_promised)} MC-N theorems, and all pinned dependencies.")


if __name__ == "__main__":
    main()
