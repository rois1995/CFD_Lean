import Integrity
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
        ("direct", toJson ([] : List String)), ("type", Json.null)]).compress)
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
    let record := Json.mkObj [
      ("name", toJson n.toString), ("module", toJson modName.toString),
      ("kind", toJson (kind ci)), ("unsafe", toJson ci.isUnsafe),
      ("root", toJson isRoot), ("axioms", toJson (ax.map Name.toString)),
      ("direct", toJson (direct.map Name.toString)),
      ("type", toJson typeText)]
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
