import Integrity
import Lean

open Lean

private def declKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

-- Select declarations by the module that introduced them, including generated ones.
run_cmd do
  let env ← getEnv
  let kernel := env.checked.get
  let owned := [`CFDLean.Core.State, `CFDLean.Core.PhysicalFlux, `CFDLean, `Integrity]
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let sourceDefs := [`CFDLean.Vector, `CFDLean.squareSum, `CFDLean.Conservative,
    `CFDLean.Primitive, `CFDLean.Conservative.pressure, `CFDLean.Conservative.Admissible,
    `CFDLean.Primitive.Admissible, `CFDLean.Primitive.toConservative,
    `CFDLean.Conservative.toPrimitive, `CFDLean.dot, `CFDLean.physicalFlux]
  let mut roots : Array Name := #[]
  for (n, idx) in env.const2ModIdx.toList do
    let modName := env.header.moduleNames[idx.toNat]!
    if owned.contains modName then
      let some ci := kernel.find? n | continue
      let inspectProof := (ci matches .thmInfo _) || sourceDefs.contains n
      if ci matches .axiomInfo _ then
        logInfo m!"AXIOM_DECL | {modName} | {n} | unsafe={ci.isUnsafe}"
      if !inspectProof then
        logInfo m!"AUX | {modName} | {declKind ci} | {n} | unsafe={ci.isUnsafe}"
        continue
      let ax := (← collectAxioms n).toList.mergeSort Name.lt
      let direct := ci.getUsedConstantsAsSet.toList.filter fun k =>
        match env.getModuleIdxFor? k with
        | some j => owned.contains env.header.moduleNames[j.toNat]!
        | none => false
      logInfo m!"DECL | {modName} | {declKind ci} | {n} | unsafe={ci.isUnsafe} | axioms={ax} | direct={direct}"
      if ax.any (fun a => !allowed.contains a) then
        throwError "unexpected axiom in {n}: {ax}"
      roots := roots.push n
  -- Follow the kernel constants in types and values, plus inductive references.
  let mut todo := roots.toList
  let mut seen : Std.HashSet Name := {}
  let mut leaves : List Name := []
  let mut unsafeReached : List Name := []
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := kernel.find? n | throwError "missing constant {n}"
    if ci.isUnsafe then unsafeReached := n :: unsafeReached
    if ci matches .axiomInfo _ then leaves := n :: leaves
    todo := ci.getUsedConstantsAsSet.toList ++ todo
  logInfo m!"CLOSURE | roots={roots.size} | visited={seen.size} | axioms={leaves.mergeSort Name.lt} | unsafe={unsafeReached}"
  if roots.isEmpty || !unsafeReached.isEmpty || leaves.any (fun a => !allowed.contains a) then
    throwError "kernel declaration inventory did not meet the policy"
