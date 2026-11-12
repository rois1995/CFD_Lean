#!/usr/bin/env bash
# Run from the rebuilt repository. Arguments: external directory for results.
set -euo pipefail
checks="$(cd "$(dirname "$0")" && pwd -P)"
out="$(realpath -m "${1:?Pass an external results directory}")"
mkdir -p "$out/control"
export LAKE_NO_CACHE=1 MATHLIB_NO_CACHE_ON_UPDATE=1
for pair in 'KernelInventory kernel-inventory' 'OriginalExamples example-axioms' 'PhysicalChecks physical-checks'; do
  read -r name log <<< "$pair"
  lake env lean -DwarningAsError=true "$checks/$name.lean" >"$out/$log.log"
done
lake env lean -R "$checks" -c "$out/control/CompilerControl.c" \
  -o "$out/control/CompilerControl.olean" "$checks/CompilerControl.lean"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean -DwarningAsError=true "$2"' \
  bash "$out/control" "$checks/InspectControl.lean" >"$out/compiler-control.log"
python3 "$checks/AuditParser.py" "$PWD" >"$out/parser-check.log"
python3 "$checks/ExactArithmetic.py" >"$out/exact-arithmetic.log"
