#!/usr/bin/env bash
# Run in a fresh checkout. Arguments: full candidate commit, external log directory.
# Requires pinned Lean/Lake, Git, Python, Node/npm, realpath and sha256sum.
set -euo pipefail
root="$(pwd -P)"
frozen="${1:?Pass the full frozen candidate commit}"
[[ "$frozen" =~ ^[0-9a-f]{40}$ ]]
out="$(realpath -m "${2:?Pass a log directory outside the checkout}")"
case "$out" in "$root"|"$root"/*) echo 'Choose a log directory outside the checkout.' >&2; exit 2;; esac
test "$(git rev-parse --show-toplevel)" = "$root"
test "$(git rev-parse HEAD)" = "$frozen"
test -z "$(git status --porcelain)"
test ! -e .lake
lean --version | grep -F 'version 4.19.0,'
mkdir -p "$out"
export MATHLIB_NO_CACHE_ON_UPDATE=1 LAKE_NO_CACHE=1 GIT_TERMINAL_PROMPT=0
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
export npm_config_audit=false npm_config_fund=false
{ lean --version; lake --version; node --version; npm --version; git --version; python3 --version; uname -sm; } >"$out/environment.log" 2>&1
sha256sum -c evidence/SHA256SUMS | tee "$out/prebuild-sha256.log"
python3 - "$out/widget-pins.json" <<'PY' | tee "$out/pins.log"
import json
import pathlib
import subprocess
import sys

root = pathlib.Path.cwd()
manifest = json.loads((root / 'lake-manifest.json').read_text())
for pin in manifest['packages']:
    path = root / manifest['packagesDir'] / pin['name']
    path.mkdir(parents=True)
    def git(*args):
        return subprocess.check_output(['git', '-C', str(path), *args], text=True).strip()
    git('init', '-q')
    git('remote', 'add', 'origin', pin['url'])
    git('fetch', '-q', '--depth=1', '--no-tags', 'origin', pin['rev'])
    git('checkout', '-q', '--detach', pin['rev'])
    assert git('rev-parse', 'HEAD') == pin['rev']
    assert not git('status', '--porcelain') and not (path / '.lake').exists()
    print(pin['name'], pin['rev'], 'fresh source checkout', flush=True)

# Used only when building the JS target as ProofWidgets' own project.
batteries = {'name': 'batteries', 'scope': 'leanprover-community', 'type': 'path',
             'dir': str(root / manifest['packagesDir'] / 'batteries'),
             'configFile': 'lakefile.toml', 'inherited': False}
pathlib.Path(sys.argv[1]).write_text(json.dumps({'version': '1.1.0', 'packages': [batteries]}))
PY
lake --no-cache -d .lake/packages/proofwidgets --packages="$out/widget-pins.json" \
  -R -v build widgetJsAll >"$out/widget-source.log" 2>&1
python3 -m unittest discover -s scripts -p test_verify.py >"$out/parser-tests.log" 2>&1
MATHLIB_NO_CACHE_ON_UPDATE=1 python3 scripts/verify.py 2>&1 | tee "$out/verify.log"
cp evidence/build.log evidence/kernel-inventory.log evidence/verification.json \
  evidence/statement-checks.log evidence/inherited-types.json evidence/bindings-diff.patch evidence/binding-type-diff.json "$out/"
python3 - "$frozen" <<'PY_COMPARE' | tee "$out/audit-comparison.log"
import hashlib
from pathlib import Path
import subprocess
import sys
for name in ["verification.json", "kernel-inventory.log", "inherited-types.json", "bindings-diff.patch", "binding-type-diff.json"]:
    actual = Path("evidence", name).read_bytes()
    expected = subprocess.check_output(["git", "show", f"{sys.argv[1]}:evidence/{name}"])
    assert actual == expected, f"Regenerated evidence changed: {name}"
    print("Exact candidate match", name, hashlib.sha256(actual).hexdigest())
PY_COMPARE
git diff --name-status "$frozen" >"$out/tracked-diff.log"
git diff --exit-code "$frozen" -- . ':(exclude)evidence/*'
git diff --exit-code "$frozen" -- evidence/SHA256SUMS
sha256sum -c evidence/SHA256SUMS >"$out/postbuild-sha256.log"
