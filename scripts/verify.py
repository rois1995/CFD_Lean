"""Build, inventory elaborated mathematical declarations, and verify the frozen contracts."""
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


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


def check_result_ids(contract, text):
    approved = re.findall(r"^\| (M2-[A-Z]+[0-9]*) \|", text, re.MULTILINE)
    bound = [result["id"] for result in contract["results"]]
    if not approved or len(bound) != len(set(bound)) or set(bound) != set(approved):
        raise ValueError("Result bindings differ from the separately frozen approved list")


def check_promises(rows, contract, stage):
    stages = ["M2a", "M2b", "M2c", "M2d"]
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


def main():
    os.chdir(ROOT)
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    contract = json.loads((ROOT / "specifications/M2-results.json").read_text())
    frozen = (ROOT / contract["contract"]).read_bytes()
    digest = hashlib.sha256(frozen).hexdigest()
    if digest != contract["contract_sha256"]:
        raise ValueError("Frozen scientific contract changed; approval amendment required")
    check_result_ids(contract, frozen.decode())
    for name, expected in contract["accepted_m1_sources"].items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
            raise ValueError(f"Accepted M1 source changed: {name}")
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
    promised = check_promises(rows, contract, contract["current_stage"])
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        path = ROOT / ".lake/packages" / package["name"]
        revision = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True)
        if revision != package["rev"] or dirty:
            raise ValueError(f"Dependency revision or tracked source mismatch: {package['name']}")
    files = [ROOT / name for name in [".gitignore", "README.md", "lean-toolchain", "lakefile.toml",
                                     "lake-manifest.json", "CFDLean.lean", "Integrity.lean", "KernelAudit.lean"]]
    for directory in ["CFDLean", "references", "specifications", "scripts"]:
        files.extend(path for path in (ROOT / directory).rglob("*")
                     if path.is_file() and "__pycache__" not in path.parts)
    (evidence / "SHA256SUMS").write_text("".join(
        f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT)}\n"
        for path in sorted(files)))
    (evidence / "verification.json").write_text(json.dumps({
        "lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
        "stage": contract["current_stage"], "promised_theorems": promised,
        "modules": sorted(modules[0]), "closure": closures[0],
        "source_modules": {module: {
            "path": module.replace(".", "/") + ".lean",
            "sha256": hashlib.sha256((ROOT / (module.replace(".", "/") + ".lean")).read_bytes()).hexdigest()
        } for module in sorted(modules[0])},
        "declarations": dict(sorted(rows.items())),
        "deferred_result_ids": [r["id"] for r in contract["results"] if ["M2a", "M2b", "M2c", "M2d"].index(r["stage"]) > ["M2a", "M2b", "M2c", "M2d"].index(contract["current_stage"])],
        "dependency_revisions_checked": len(manifest["packages"]),
        "m1_acceptance_record": "reviews/M1/CFD_Lean_M1_Acceptance.md",
        "m2_approval_record": contract["approval_record"], "m2_independent_acceptance": "pending"
    }, indent=2) + "\n")
    print(f"Verified {len(rows)} qualified inventory records, {len(promised)} promised theorems, and all pinned dependencies.")


if __name__ == "__main__":
    main()
