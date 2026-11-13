#!/usr/bin/env bash
# Run from the candidate. Uses only an external temporary module and audit driver.
set -euo pipefail
src="$(cd ../checks/fixtures && pwd)"
logs="$(cd ../logs && pwd)"
aux="$logs/fixture-build"
mkdir -p "$aux/CFDLean"
# Lean resolves a whole namespace from the first directory containing its prefix.
# Link the already verified project modules into this external fixture overlay.
ln -sfn "$PWD/.lake/build/lib/lean/CFDLean.olean" "$aux/CFDLean.olean"
ln -sfn "$PWD/.lake/build/lib/lean/CFDLean/Core" "$aux/CFDLean/Core"
lake env lean -R "$src" -o "$aux/Foreign.olean" "$src/Foreign.lean"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean -R "$2" -o "$1/CFDLean/AuditFixture.olean" "$2/CFDLean/AuditFixture.lean"' bash "$aux" "$src"
{ echo 'import CFDLean.AuditFixture'; cat KernelAudit.lean; } >"$aux/AuditNegative.lean"
if lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean -DwarningAsError=true "$1/AuditNegative.lean"' bash "$aux" >"$aux/out.log" 2>&1; then exit 1; fi
grep -F 'unapproved axiom in CFDLean.AuditFixture.fixtureClaim' "$aux/out.log" >"$logs/negative-control.log"
grep -F 'ReviewerFixture.extra' "$logs/negative-control.log"
