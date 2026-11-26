import Integrity
import CFDLean.Verification.BurgersB0Verify
import CFDLean.Verification.BurgersB1Verify
import CFDLean.Verification.BurgersB2Verify
import CFDLean.Verification.BurgersB3Verify
import CFDLean.Verification.BurgersB3bVerify
import CFDLean.Verification.BurgersB4Verify
import CFDLean.Verification.BurgersE0Verify
import CFDLean.Verification.BurgersE0bVerify
import CFDLean.Verification.JST1Verify
import Lean

open Lean

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

run_cmd do
  let env ← getEnv
  let kernel := env.checked.get
  let owns := fun n : Name => n == `CFDLean || (`CFDLean).isPrefixOf n || n == `Integrity
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut roots : Array Name := #[]
  let mut modules : Array String := #[]
  for modName in env.header.moduleNames do
    if owns modName then modules := modules.push modName.toString
  logInfo ("CFDLEAN_MODULES " ++ (toJson modules).compress)
  for (n, idx) in env.const2ModIdx.toList do
    let modName := env.header.moduleNames[idx.toNat]!
    if !owns modName then continue
    let some ci := kernel.find? n | do
      logInfo ("CFDLEAN_DECL " ++ (Json.mkObj [
        ("name", toJson n.toString), ("module", toJson modName.toString),
        ("kind", toJson "compiler_metadata_only"), ("unsafe", Json.null),
        ("root", toJson false), ("axioms", toJson ([] : List String)),
        ("direct", toJson ([] : List String)), ("type", Json.null), ("raw_type", Json.null)]).compress)
      continue
    if (ci matches .axiomInfo _) && !ci.isUnsafe then
      throwError "explicit project axiom {n}"
    let isRoot := !ci.isUnsafe
    let ax ← if isRoot then do
      let found ← collectAxioms n
      pure (found.toList.mergeSort Name.lt)
    else pure []
    if ax.any (fun a => !allowed.contains a) then
      throwError "unapproved axiom in {n}: {ax}"
    let direct := ci.getUsedConstantsAsSet.toList.filter fun k =>
      match env.getModuleIdxFor? k with
      | some j => owns env.header.moduleNames[j.toNat]!
      | none => false
    let typeText ← Lean.Elab.Command.liftTermElabM do
      return toString (← Lean.PrettyPrinter.ppExpr ci.type)
    -- MR-3: theorem types also without notation and coercions (`raw_type`), compared by `scripts/verify.py`.
    let rawText ← if ci matches .thmInfo _ then
        Lean.Elab.Command.liftTermElabM do
          withOptions (fun o => (o.setBool `pp.notation false).setBool `pp.coercions false) do
            return Json.str (toString (← Lean.PrettyPrinter.ppExpr ci.type))
      else pure Json.null
    let record := Json.mkObj [
      ("name", toJson n.toString), ("module", toJson modName.toString),
      ("kind", toJson (kind ci)), ("unsafe", toJson ci.isUnsafe),
      ("root", toJson isRoot), ("axioms", toJson (ax.map Name.toString)),
      ("direct", toJson (direct.map Name.toString)),
      ("type", toJson typeText), ("raw_type", rawText)]
    logInfo ("CFDLEAN_DECL " ++ record.compress)
    if isRoot then roots := roots.push n
  let mut todo := roots.toList
  let mut seen : Std.HashSet Name := {}
  let mut leaves : List Name := []
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := kernel.find? n | throwError "missing dependency {n}"
    if ci.isUnsafe then throwError "unsafe dependency reached from a mathematical root: {n}"
    if ci matches .axiomInfo _ then leaves := n :: leaves
    todo := ci.getUsedConstantsAsSet.toList ++ todo
  if roots.isEmpty || leaves.any (fun a => !allowed.contains a) then
    throwError "kernel inventory failed the foundation policy"
  logInfo ("CFDLEAN_CLOSURE " ++ (Json.mkObj [
    ("roots", toJson roots.size), ("visited", toJson seen.size),
    ("axioms", toJson ((leaves.mergeSort Name.lt).map Name.toString)),
    ("unsafe_reached", toJson ([] : List String))]).compress)

/-! JST1 (MR-2): each of the 92 frozen paper-1 statements is bound to its proof. The axioms of every proof are in
the `CFDLEAN_DECL` records above (`scripts/verify.py` checks them against `specifications/JST1/P*-results.json`). -/

example : CFDLean.JST1.Spec.P1_1_0 := CFDLean.JST1.Proofs.p1_1_0
example : CFDLean.JST1.Spec.P1_1_1 := CFDLean.JST1.Proofs.p1_1_1
example : CFDLean.JST1.Spec.P1_1_2 := CFDLean.JST1.Proofs.p1_1_2
example : CFDLean.JST1.Spec.P1_1_3 := CFDLean.JST1.Proofs.p1_1_3
example : CFDLean.JST1.Spec.P1_1_4 := CFDLean.JST1.Proofs.p1_1_4
example : CFDLean.JST1.Spec.P1_1_5 := CFDLean.JST1.Proofs.p1_1_5
example : CFDLean.JST1.Spec.P1_1_6 := CFDLean.JST1.Proofs.p1_1_6
example : CFDLean.JST1.Spec.P1_2_0 := CFDLean.JST1.Proofs.p1_2_0
example : CFDLean.JST1.Spec.P1_2_1 := CFDLean.JST1.Proofs.p1_2_1
example : CFDLean.JST1.Spec.P1_2_2 := CFDLean.JST1.Proofs.p1_2_2
example : CFDLean.JST1.Spec.P1_2_3 := CFDLean.JST1.Proofs.p1_2_3
example : CFDLean.JST1.Spec.P1_2_4 := CFDLean.JST1.Proofs.p1_2_4
example : CFDLean.JST1.Spec.P1_2_5 := CFDLean.JST1.Proofs.p1_2_5
example : CFDLean.JST1.Spec.P1_2_6 := CFDLean.JST1.Proofs.p1_2_6
example : CFDLean.JST1.Spec.P1_2_7 := CFDLean.JST1.Proofs.p1_2_7
example : CFDLean.JST1.Spec.P1_3_1 := CFDLean.JST1.Proofs.p1_3_1
example : CFDLean.JST1.Spec.P1_3_2 := CFDLean.JST1.Proofs.p1_3_2
example : CFDLean.JST1.Spec.P1_3_3 := CFDLean.JST1.Proofs.p1_3_3
example : CFDLean.JST1.Spec.P1_3_4 := CFDLean.JST1.Proofs.p1_3_4
example : CFDLean.JST1.Spec.P1_4_0 := CFDLean.JST1.Proofs.p1_4_0
example : CFDLean.JST1.Spec.P1_4_1 := CFDLean.JST1.Proofs.p1_4_1
example : CFDLean.JST1.Spec.P1_4_2 := CFDLean.JST1.Proofs.p1_4_2
example : CFDLean.JST1.Spec.P1_4_3 := CFDLean.JST1.Proofs.p1_4_3
example : CFDLean.JST1.Spec.P1_4_3b := CFDLean.JST1.Proofs.p1_4_3b
example : CFDLean.JST1.Spec.P1_4_4 := CFDLean.JST1.Proofs.p1_4_4
example : CFDLean.JST1.Spec.P1_5_0a := CFDLean.JST1.Proofs.p1_5_0a
example : CFDLean.JST1.Spec.P1_5_0b := CFDLean.JST1.Proofs.p1_5_0b
example : CFDLean.JST1.Spec.P1_5_1 := CFDLean.JST1.Proofs.p1_5_1
example : CFDLean.JST1.Spec.P1_5_2 := CFDLean.JST1.Proofs.p1_5_2
example : CFDLean.JST1.Spec.P1_5_3 := CFDLean.JST1.Proofs.p1_5_3
example : CFDLean.JST1.Spec.P1_5_4 := CFDLean.JST1.Proofs.p1_5_4
example : CFDLean.JST1.Spec.P1_5_4b := CFDLean.JST1.Proofs.p1_5_4b
example : CFDLean.JST1.Spec.P1_5_5 := CFDLean.JST1.Proofs.p1_5_5
example : CFDLean.JST1.Spec.P1_5_6 := CFDLean.JST1.Proofs.p1_5_6
example : CFDLean.JST1.Spec.P1_5_7 := CFDLean.JST1.Proofs.p1_5_7
example : CFDLean.JST1.Spec.P1_5_8 := CFDLean.JST1.Proofs.p1_5_8
example : CFDLean.JST1.Spec.P2_6_1 := CFDLean.JST1.Proofs.p2_6_1
example : CFDLean.JST1.Spec.P2_6_2 := CFDLean.JST1.Proofs.p2_6_2
example : CFDLean.JST1.Spec.P2_6_3 := CFDLean.JST1.Proofs.p2_6_3
example : CFDLean.JST1.Spec.P2_6_4 := CFDLean.JST1.Proofs.p2_6_4
example : CFDLean.JST1.Spec.P2_6_5 := CFDLean.JST1.Proofs.p2_6_5
example : CFDLean.JST1.Spec.P2_6_5b := CFDLean.JST1.Proofs.p2_6_5b
example : CFDLean.JST1.Spec.P2_6_6 := CFDLean.JST1.Proofs.p2_6_6
example : CFDLean.JST1.Spec.P2_6_7 := CFDLean.JST1.Proofs.p2_6_7
example : CFDLean.JST1.Spec.P2_7_1 := CFDLean.JST1.Proofs.p2_7_1
example : CFDLean.JST1.Spec.P2_7_2 := CFDLean.JST1.Proofs.p2_7_2
example : CFDLean.JST1.Spec.P2_7_3 := CFDLean.JST1.Proofs.p2_7_3
example : CFDLean.JST1.Spec.P2_7_4 := CFDLean.JST1.Proofs.p2_7_4
example : CFDLean.JST1.Spec.P2_8_0 := CFDLean.JST1.Proofs.p2_8_0
example : CFDLean.JST1.Spec.P2_8_1 := CFDLean.JST1.Proofs.p2_8_1
example : CFDLean.JST1.Spec.P2_8_2 := CFDLean.JST1.Proofs.p2_8_2
example : CFDLean.JST1.Spec.P2_8_3 := CFDLean.JST1.Proofs.p2_8_3
example : CFDLean.JST1.Spec.P2_8_4 := CFDLean.JST1.Proofs.p2_8_4
example : CFDLean.JST1.Spec.P2_8_5 := CFDLean.JST1.Proofs.p2_8_5
example : CFDLean.JST1.Spec.P2_8_6 := CFDLean.JST1.Proofs.p2_8_6
example : CFDLean.JST1.Spec.P2_9_0 := CFDLean.JST1.Proofs.p2_9_0
example : CFDLean.JST1.Spec.P2_9_1 := CFDLean.JST1.Proofs.p2_9_1
example : CFDLean.JST1.Spec.P2_9_2 := CFDLean.JST1.Proofs.p2_9_2
example : CFDLean.JST1.Spec.P2_9_3 := CFDLean.JST1.Proofs.p2_9_3
example : CFDLean.JST1.Spec.P2_9_4 := CFDLean.JST1.Proofs.p2_9_4
example : CFDLean.JST1.Spec.P2_10_1 := CFDLean.JST1.Proofs.p2_10_1
example : CFDLean.JST1.Spec.P2_10_2 := CFDLean.JST1.Proofs.p2_10_2
example : CFDLean.JST1.Spec.P2_10_3 := CFDLean.JST1.Proofs.p2_10_3
example : CFDLean.JST1.Spec.P2_10_4 := CFDLean.JST1.Proofs.p2_10_4
example : CFDLean.JST1.Spec.P2_10_5 := CFDLean.JST1.Proofs.p2_10_5
example : CFDLean.JST1.Spec.P2_10_6 := CFDLean.JST1.Proofs.p2_10_6
example : CFDLean.JST1.Spec.P2_10_7 := CFDLean.JST1.Proofs.p2_10_7
example : CFDLean.JST1.Spec.P2_10_8 := CFDLean.JST1.Proofs.p2_10_8
example : CFDLean.JST1.Spec.P2_8_0b := CFDLean.JST1.Proofs.p2_8_0b
example : CFDLean.JST1.Spec.P2_9_2b := CFDLean.JST1.Proofs.p2_9_2b
example : CFDLean.JST1.Spec.P2_10_8b := CFDLean.JST1.Proofs.p2_10_8b
example : CFDLean.JST1.Spec.P2_10_8c := CFDLean.JST1.Proofs.p2_10_8c
example : CFDLean.JST1.Spec.P3_11_1 := CFDLean.JST1.Proofs.p3_11_1
example : CFDLean.JST1.Spec.P3_11_2 := CFDLean.JST1.Proofs.p3_11_2
example : CFDLean.JST1.Spec.P3_11_3 := CFDLean.JST1.Proofs.p3_11_3
example : CFDLean.JST1.Spec.P3_12_1 := CFDLean.JST1.Proofs.p3_12_1
example : CFDLean.JST1.Spec.P3_12_2 := CFDLean.JST1.Proofs.p3_12_2
example : CFDLean.JST1.Spec.P3_12_3 := CFDLean.JST1.Proofs.p3_12_3
example : CFDLean.JST1.Spec.P3_12_4 := CFDLean.JST1.Proofs.p3_12_4
example : CFDLean.JST1.Spec.P3_12_5 := CFDLean.JST1.Proofs.p3_12_5
example : CFDLean.JST1.Spec.P3_13_1 := CFDLean.JST1.Proofs.p3_13_1
example : CFDLean.JST1.Spec.P3_13_2 := CFDLean.JST1.Proofs.p3_13_2
example : CFDLean.JST1.Spec.P3_11_2b := CFDLean.JST1.Proofs.p3_11_2b
example : CFDLean.JST1.Spec.P3_11_4 := CFDLean.JST1.Proofs.p3_11_4
example : CFDLean.JST1.Spec.P3_11_4b := CFDLean.JST1.Proofs.p3_11_4b
example : CFDLean.JST1.Spec.P3_11_5 := CFDLean.JST1.Proofs.p3_11_5
example : CFDLean.JST1.Spec.P3_11_6 := CFDLean.JST1.Proofs.p3_11_6
example : CFDLean.JST1.Spec.P3_14_1 := CFDLean.JST1.Proofs.p3_14_1
example : CFDLean.JST1.Spec.P3_14_2 := CFDLean.JST1.Proofs.p3_14_2
example : CFDLean.JST1.Spec.P3_14_3 := CFDLean.JST1.Proofs.p3_14_3
example : CFDLean.JST1.Spec.P3_11_7 := CFDLean.JST1.Proofs.p3_11_7
example : CFDLean.JST1.Spec.P3_11_8 := CFDLean.JST1.Proofs.p3_11_8
