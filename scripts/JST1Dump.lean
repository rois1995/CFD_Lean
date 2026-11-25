import CFDLean
import Lean

/-! JST1 (MR-2) evidence: print the 92 bound statement definitions `CFDLean.JST1.Spec.P*` with the settings of the
JST_Paper_Lean statement dumps (`scripts/DumpStmts.lean`: `STMT`, `pp.fullNames`; `scripts/DumpStmtsRaw.lean`: `XSTMT`,
no notation, no coercions, `pp.funBinderTypes`), and the resolution check `JST1DEP`. Run with
`lake env lean scripts/JST1Dump.lean`; output in `evidence/JST1/statements-cfd.txt` (comparison:
`evidence/JST1/fold-diff.md`). -/
open Lean Elab Command

set_option pp.fullNames true in
set_option format.width 100000 in
elab "#dumpjst1" : command => do
  let env ← getEnv
  for n in [`CFDLean.JST1.Spec.P1_1_0,`CFDLean.JST1.Spec.P1_1_1,`CFDLean.JST1.Spec.P1_1_2,`CFDLean.JST1.Spec.P1_1_3,`CFDLean.JST1.Spec.P1_1_4,`CFDLean.JST1.Spec.P1_1_5,`CFDLean.JST1.Spec.P1_1_6,`CFDLean.JST1.Spec.P1_2_0,`CFDLean.JST1.Spec.P1_2_1,`CFDLean.JST1.Spec.P1_2_2,`CFDLean.JST1.Spec.P1_2_3,`CFDLean.JST1.Spec.P1_2_4,`CFDLean.JST1.Spec.P1_2_5,`CFDLean.JST1.Spec.P1_2_6,`CFDLean.JST1.Spec.P1_2_7,`CFDLean.JST1.Spec.P1_3_1,`CFDLean.JST1.Spec.P1_3_2,`CFDLean.JST1.Spec.P1_3_3,`CFDLean.JST1.Spec.P1_3_4,`CFDLean.JST1.Spec.P1_4_0,`CFDLean.JST1.Spec.P1_4_1,`CFDLean.JST1.Spec.P1_4_2,`CFDLean.JST1.Spec.P1_4_3,`CFDLean.JST1.Spec.P1_4_3b,`CFDLean.JST1.Spec.P1_4_4,`CFDLean.JST1.Spec.P1_5_0a,`CFDLean.JST1.Spec.P1_5_0b,`CFDLean.JST1.Spec.P1_5_1,`CFDLean.JST1.Spec.P1_5_2,`CFDLean.JST1.Spec.P1_5_3,`CFDLean.JST1.Spec.P1_5_4,`CFDLean.JST1.Spec.P1_5_4b,`CFDLean.JST1.Spec.P1_5_5,`CFDLean.JST1.Spec.P1_5_6,`CFDLean.JST1.Spec.P1_5_7,`CFDLean.JST1.Spec.P1_5_8,`CFDLean.JST1.Spec.P2_6_1,`CFDLean.JST1.Spec.P2_6_2,`CFDLean.JST1.Spec.P2_6_3,`CFDLean.JST1.Spec.P2_6_4,`CFDLean.JST1.Spec.P2_6_5,`CFDLean.JST1.Spec.P2_6_5b,`CFDLean.JST1.Spec.P2_6_6,`CFDLean.JST1.Spec.P2_6_7,`CFDLean.JST1.Spec.P2_7_1,`CFDLean.JST1.Spec.P2_7_2,`CFDLean.JST1.Spec.P2_7_3,`CFDLean.JST1.Spec.P2_7_4,`CFDLean.JST1.Spec.P2_8_0,`CFDLean.JST1.Spec.P2_8_1,`CFDLean.JST1.Spec.P2_8_2,`CFDLean.JST1.Spec.P2_8_3,`CFDLean.JST1.Spec.P2_8_4,`CFDLean.JST1.Spec.P2_8_5,`CFDLean.JST1.Spec.P2_8_6,`CFDLean.JST1.Spec.P2_9_0,`CFDLean.JST1.Spec.P2_9_1,`CFDLean.JST1.Spec.P2_9_2,`CFDLean.JST1.Spec.P2_9_3,`CFDLean.JST1.Spec.P2_9_4,`CFDLean.JST1.Spec.P2_10_1,`CFDLean.JST1.Spec.P2_10_2,`CFDLean.JST1.Spec.P2_10_3,`CFDLean.JST1.Spec.P2_10_4,`CFDLean.JST1.Spec.P2_10_5,`CFDLean.JST1.Spec.P2_10_6,`CFDLean.JST1.Spec.P2_10_7,`CFDLean.JST1.Spec.P2_10_8,`CFDLean.JST1.Spec.P2_8_0b,`CFDLean.JST1.Spec.P2_9_2b,`CFDLean.JST1.Spec.P2_10_8b,`CFDLean.JST1.Spec.P2_10_8c,`CFDLean.JST1.Spec.P3_11_1,`CFDLean.JST1.Spec.P3_11_2,`CFDLean.JST1.Spec.P3_11_3,`CFDLean.JST1.Spec.P3_12_1,`CFDLean.JST1.Spec.P3_12_2,`CFDLean.JST1.Spec.P3_12_3,`CFDLean.JST1.Spec.P3_12_4,`CFDLean.JST1.Spec.P3_12_5,`CFDLean.JST1.Spec.P3_13_1,`CFDLean.JST1.Spec.P3_13_2,`CFDLean.JST1.Spec.P3_11_2b,`CFDLean.JST1.Spec.P3_11_4,`CFDLean.JST1.Spec.P3_11_4b,`CFDLean.JST1.Spec.P3_11_5,`CFDLean.JST1.Spec.P3_11_6,`CFDLean.JST1.Spec.P3_14_1,`CFDLean.JST1.Spec.P3_14_2,`CFDLean.JST1.Spec.P3_14_3,`CFDLean.JST1.Spec.P3_11_7,`CFDLean.JST1.Spec.P3_11_8] do
    match env.find? n with
    | some (.defnInfo d) =>
        let fmt ← liftTermElabM <| Meta.ppExpr d.value
        logInfo m!"STMT {n} :: {fmt}"
    | _ => logInfo m!"STMT {n} :: MISSING"

set_option pp.fullNames true in
set_option format.width 100000 in
#dumpjst1

/-! Resolution check (`JST1DEP`): every constant used by a JST1 definition (type and value; statement and definition
modules, not `Proofs`) that lies in `CFDLean` outside `CFDLean.JST1`. Inside `namespace CFDLean.JST1` an unqualified
name resolves to `CFDLean.<name>` before an `open CFDLean.Num`, so this list shows that no identifier of the folded
sources was captured by an M1-M5 constant: it may contain only `CFDLean.Num.*` and the `CFDLean.MedianDual.*`
constants that the JST sources name with their full `CFDLean.` prefix. -/

elab "#depjst1" : command => do
  let env ← getEnv
  let mut found : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    if !(`CFDLean.Papers.JST1).isPrefixOf modName || (`CFDLean.Papers.JST1.Proofs).isPrefixOf modName then continue
    let used := ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[]
    for k in used do
      if (`CFDLean).isPrefixOf k && !(`CFDLean.JST1).isPrefixOf k then
        found := found.push s!"{n} -> {k}"
  for line in found.qsort (· < ·) do
    logInfo m!"JST1DEP {line}"

#depjst1

set_option pp.coercions false
set_option pp.notation false
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.funBinderTypes true
set_option format.width 1000000

elab "#dumpjst1raw" : command => do
  let env ← getEnv
  for n in [`CFDLean.JST1.Spec.P1_1_0,`CFDLean.JST1.Spec.P1_1_1,`CFDLean.JST1.Spec.P1_1_2,`CFDLean.JST1.Spec.P1_1_3,`CFDLean.JST1.Spec.P1_1_4,`CFDLean.JST1.Spec.P1_1_5,`CFDLean.JST1.Spec.P1_1_6,`CFDLean.JST1.Spec.P1_2_0,`CFDLean.JST1.Spec.P1_2_1,`CFDLean.JST1.Spec.P1_2_2,`CFDLean.JST1.Spec.P1_2_3,`CFDLean.JST1.Spec.P1_2_4,`CFDLean.JST1.Spec.P1_2_5,`CFDLean.JST1.Spec.P1_2_6,`CFDLean.JST1.Spec.P1_2_7,`CFDLean.JST1.Spec.P1_3_1,`CFDLean.JST1.Spec.P1_3_2,`CFDLean.JST1.Spec.P1_3_3,`CFDLean.JST1.Spec.P1_3_4,`CFDLean.JST1.Spec.P1_4_0,`CFDLean.JST1.Spec.P1_4_1,`CFDLean.JST1.Spec.P1_4_2,`CFDLean.JST1.Spec.P1_4_3,`CFDLean.JST1.Spec.P1_4_3b,`CFDLean.JST1.Spec.P1_4_4,`CFDLean.JST1.Spec.P1_5_0a,`CFDLean.JST1.Spec.P1_5_0b,`CFDLean.JST1.Spec.P1_5_1,`CFDLean.JST1.Spec.P1_5_2,`CFDLean.JST1.Spec.P1_5_3,`CFDLean.JST1.Spec.P1_5_4,`CFDLean.JST1.Spec.P1_5_4b,`CFDLean.JST1.Spec.P1_5_5,`CFDLean.JST1.Spec.P1_5_6,`CFDLean.JST1.Spec.P1_5_7,`CFDLean.JST1.Spec.P1_5_8,`CFDLean.JST1.Spec.P2_6_1,`CFDLean.JST1.Spec.P2_6_2,`CFDLean.JST1.Spec.P2_6_3,`CFDLean.JST1.Spec.P2_6_4,`CFDLean.JST1.Spec.P2_6_5,`CFDLean.JST1.Spec.P2_6_5b,`CFDLean.JST1.Spec.P2_6_6,`CFDLean.JST1.Spec.P2_6_7,`CFDLean.JST1.Spec.P2_7_1,`CFDLean.JST1.Spec.P2_7_2,`CFDLean.JST1.Spec.P2_7_3,`CFDLean.JST1.Spec.P2_7_4,`CFDLean.JST1.Spec.P2_8_0,`CFDLean.JST1.Spec.P2_8_1,`CFDLean.JST1.Spec.P2_8_2,`CFDLean.JST1.Spec.P2_8_3,`CFDLean.JST1.Spec.P2_8_4,`CFDLean.JST1.Spec.P2_8_5,`CFDLean.JST1.Spec.P2_8_6,`CFDLean.JST1.Spec.P2_9_0,`CFDLean.JST1.Spec.P2_9_1,`CFDLean.JST1.Spec.P2_9_2,`CFDLean.JST1.Spec.P2_9_3,`CFDLean.JST1.Spec.P2_9_4,`CFDLean.JST1.Spec.P2_10_1,`CFDLean.JST1.Spec.P2_10_2,`CFDLean.JST1.Spec.P2_10_3,`CFDLean.JST1.Spec.P2_10_4,`CFDLean.JST1.Spec.P2_10_5,`CFDLean.JST1.Spec.P2_10_6,`CFDLean.JST1.Spec.P2_10_7,`CFDLean.JST1.Spec.P2_10_8,`CFDLean.JST1.Spec.P2_8_0b,`CFDLean.JST1.Spec.P2_9_2b,`CFDLean.JST1.Spec.P2_10_8b,`CFDLean.JST1.Spec.P2_10_8c,`CFDLean.JST1.Spec.P3_11_1,`CFDLean.JST1.Spec.P3_11_2,`CFDLean.JST1.Spec.P3_11_3,`CFDLean.JST1.Spec.P3_12_1,`CFDLean.JST1.Spec.P3_12_2,`CFDLean.JST1.Spec.P3_12_3,`CFDLean.JST1.Spec.P3_12_4,`CFDLean.JST1.Spec.P3_12_5,`CFDLean.JST1.Spec.P3_13_1,`CFDLean.JST1.Spec.P3_13_2,`CFDLean.JST1.Spec.P3_11_2b,`CFDLean.JST1.Spec.P3_11_4,`CFDLean.JST1.Spec.P3_11_4b,`CFDLean.JST1.Spec.P3_11_5,`CFDLean.JST1.Spec.P3_11_6,`CFDLean.JST1.Spec.P3_14_1,`CFDLean.JST1.Spec.P3_14_2,`CFDLean.JST1.Spec.P3_14_3,`CFDLean.JST1.Spec.P3_11_7,`CFDLean.JST1.Spec.P3_11_8] do
    match env.find? n with
    | some (.defnInfo d) =>
        let s ← liftTermElabM do return toString (← Meta.ppExpr d.value)
        logInfo m!"XSTMT {n} :: {s}"
    | _ => logInfo m!"XSTMT {n} :: MISSING"

#dumpjst1raw
