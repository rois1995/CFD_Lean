#!/usr/bin/env bash
set -euo pipefail
# Working directory is the verified candidate; the toolchain is already on PATH.
review="$(cd ../checks && pwd)"
logs="$(cd ../logs && pwd)"
mkdir -p "$logs/control"
export MATHLIB_NO_CACHE_ON_UPDATE=1 LAKE_NO_CACHE=1 LEAN_NUM_THREADS=2
lake env lean -DwarningAsError=true "$review/CheckBindings.lean" >"$logs/expected-types.log" 2>&1
lake env lean -DwarningAsError=true "$review/Independent.lean" >"$logs/independent-kernel.log" 2>&1
lake env lean -R "$review" -c "$logs/control/AuxProvenance.c" -o "$logs/control/AuxProvenance.olean" "$review/AuxProvenance.lean"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean -DwarningAsError=true "$2"' bash "$logs/control" "$review/InspectAux.lean" >"$logs/projection-control.log"
lake env lean -DwarningAsError=true reviews/M1/reviewer/OriginalExamples.lean >"$logs/original-examples.log"
python3 "$review/VerifyEvidence.py" >"$logs/comparison.log"
