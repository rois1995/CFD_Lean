import CFDLean
import Integrity
import Lean

open Lean
open CFDLean
open CFDLean.Coordinates CFDLean.PhysicalJacobian

-- State the link using the accepted flux directly.
example (g : ℝ) (n : Vector 3) (x : StateCoordinates) (hr : x 0 ≠ 0) :
    HasFDerivAt (fun y => encode (physicalFlux g (decode y) n)) (jacobian g x n) x :=
  hasFDerivAt_coordinateFlux g n x hr

example (g : ℝ) (S : Vector 3) (x : StateCoordinates) (hr : x 0 ≠ 0) (hs : S ≠ 0) :
    HasFDerivAt (fun y => encode (physicalFlux g (decode y) S)) (area S • jacobian g x (unitNormal S)) x :=
  hasFDerivAt_integratedFlux g S x hr hs

example (g : ℝ) (x : StateCoordinates) : HasFDerivAt (𝕜 := ℝ)
    (fun y => encode (physicalFlux g (decode y) (0 : Vector 3))) 0 x :=
  hasFDerivAt_zeroArea g x

run_cmd do
  let env ← getEnv
  let k := env.checked.get
  let owned := fun n : Name => n == `Integrity || (`CFDLean).isPrefixOf n
  let mut pending : List Name := []
  for (name, ix) in env.const2ModIdx.toList do
    if owned env.header.moduleNames[ix.toNat]! then
      if let some info := k.find? name then
        if !info.isUnsafe then pending := name :: pending
  let roots := pending.length
  let mut visited : Std.HashSet Name := {}
  let mut axioms : List Name := []
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if visited.contains name then continue
    visited := visited.insert name
    let some info := k.find? name | throwError "missing dependency {name}"
    if info.isUnsafe then throwError "reachable unsafe {name}"
    if info matches .axiomInfo _ then axioms := name :: axioms
    pending := info.type.getUsedConstants.toList ++ pending
    if let some body := info.value? true then pending := body.getUsedConstants.toList ++ pending
    match info with
    | .inductInfo v => pending := v.ctors ++ pending
    | .recInfo v =>
      pending := v.all ++ pending
      for rule in v.rules do pending := rule.ctor :: (rule.rhs.getUsedConstants.toList ++ pending)
    | _ => pure ()
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  if axioms.any (fun a => !(allowed.contains a)) then
    throwError "extra axiom {axioms}"
  logInfo m!"roots={roots} constants={visited.size} axioms={axioms.mergeSort Name.lt}"
