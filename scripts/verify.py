"""Build the pinned package, audit transitive axioms, and record source hashes."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PATTERN = re.compile(
    r"'CFDLean\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
)


def parse_axioms(output):
    # shortcut: M1 has unique theorem rows; reject duplicates and inventory modules before later milestones.
    return {name: set(filter(None, (x.strip() for x in (axioms or "").split(","))))
            for name, axioms in PATTERN.findall(output)}


# Check that the parser exposes a forbidden transitive axiom and handles axiom-free proofs.
assert parse_axioms("'CFDLean.bad' depends on axioms: [propext, sorryAx]")["bad"] - ALLOWED == {"sorryAx"}
assert parse_axioms("'CFDLean.good' does not depend on any axioms") == {"good": set()}

os.chdir(ROOT)
evidence = ROOT / "evidence"
evidence.mkdir(exist_ok=True)
env = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1")
with (evidence / "build.log").open("w") as log:
    subprocess.run(["lake", "build"], env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
result = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "Integrity.lean"],
                        env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(evidence / "axioms.log").write_text(result.stdout)
result.check_returncode()
axioms = parse_axioms(result.stdout)
source_files = sorted((ROOT / "CFDLean").rglob("*.lean"))
declared = {name for path in source_files
            for name in re.findall(r"^theorem\s+(\w+)", path.read_text(), re.MULTILINE)}
if set(axioms) != declared:
    raise RuntimeError(f"Axiom audit coverage differs: {set(axioms) ^ declared}")
for name, dependencies in axioms.items():
    if dependencies - ALLOWED:
        raise RuntimeError(f"Forbidden transitive axioms in {name}: {dependencies - ALLOWED}")
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
for package in manifest["packages"]:
    path = ROOT / ".lake/packages" / package["name"]
    revision = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(
        ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True)
    if revision != package["rev"] or dirty:
        raise RuntimeError(f"Dependency revision or tracked source mismatch: {package['name']}")
files = [ROOT / name for name in [".gitignore", "README.md", "lean-toolchain", "lakefile.toml",
                                 "lake-manifest.json", "CFDLean.lean", "Integrity.lean"]]
for directory in ["CFDLean", "references", "specifications", "scripts"]:
    files.extend(path for path in (ROOT / directory).rglob("*") if path.is_file())
(evidence / "SHA256SUMS").write_text("".join(
    f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT)}\n"
    for path in sorted(files)))
(evidence / "verification.json").write_text(json.dumps({
    "lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
    "project_theorems": len(declared),
    "transitive_axioms": {name: sorted(deps) for name, deps in sorted(axioms.items())},
    "dependency_revisions_checked": len(manifest["packages"]),
    "independent_review": "pending"
}, indent=2) + "\n")
print(f"Verified build, all {len(declared)} project theorem axiom lists, and all pinned dependencies.")
