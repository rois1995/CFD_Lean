import CFDLean
import Integrity
import Lean
set_option maxRecDepth 4096
open Lean CFDLean Coordinates PhysicalJacobian Roe Roe.Spectral

-- Chain the actual integrated M1 flux jump directly to the explicit CB-inverse operator.
example (g : ℝ) (S : CFDLean.Vector 3) (x y : StateCoordinates)
    (hg : 1 < g) (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) :
    let z := midpoint g x y
    C g S z (inverseB g z (y-x)) =
      encode (physicalFlux g (decode y) S) - encode (physicalFlux g (decode x) S) := by
  dsimp only
  have hs := secant_identity g S x y hg hx hy
  rw [roeMatrix_CB_inverse g S x y hg hx hy] at hs
  exact hs

-- Check the operator limit and derivative refer to a single physical target.
example (g : ℝ) (n : CFDLean.Vector 3) (x : StateCoordinates) (hx : (decode x).Admissible g) :
    ∃ A : StateCoordinates →L[ℝ] StateCoordinates,
      HasFDerivAt (fun w => encode (physicalFlux g (decode w) n)) A x ∧
      Filter.Tendsto (fun p : StateCoordinates × StateCoordinates => roeMatrix g p.1 p.2 n)
        (nhds (x,x)) (nhds A) :=
  ⟨jacobian g x n, hasFDerivAt_coordinateFlux g n x (ne_of_gt hx.1),
   roeMatrix_equal_state_limit g x n hx⟩

run_cmd do
  let env ← getEnv
  let ker := env.checked.get
  let mut todo : List Name := []
  for (n,i) in env.const2ModIdx.toList do
    let m := env.header.moduleNames[i.toNat]!
    if m == `Integrity || (`CFDLean).isPrefixOf m then
      if let some ci := ker.find? n then
        if !ci.isUnsafe then todo := n :: todo
  let roots := todo.length
  let mut seen : Std.HashSet Name := {}
  let mut leaves : List Name := []
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := ker.find? n | throwError "missing {n}"
    if ci.isUnsafe then throwError "unsafe {n}"
    if ci matches .axiomInfo _ then leaves := n :: leaves
    todo := ci.type.getUsedConstants.toList ++ todo
    if let some v := ci.value? true then todo := v.getUsedConstants.toList ++ todo
    match ci with
    | .inductInfo v => todo := v.ctors ++ todo
    | .recInfo v =>
      todo := v.all ++ todo
      for r in v.rules do todo := r.ctor :: (r.rhs.getUsedConstants.toList ++ todo)
    | _ => pure ()
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  if leaves.any (fun n => !(allowed.contains n)) then throwError "extra axiom"
  logInfo m!"Independent roots={roots} visited={seen.size} axioms={leaves.mergeSort Name.lt}; no reachable unsafe constant"

-- Compose the actual public flux with every complete eigenbasis.
example {ι : Type*} [Fintype ι] (g : ℝ) (U V : Conservative 3) (S : Vector 3)
    (hg : 1 < g) (hU : U.Admissible g) (hV : V.Admissible g) (hS : S ≠ 0)
    (bas : Basis ι ℝ StateCoordinates) (mu : ι → ℝ)
    (he : ∀ i, roeMatrix g (encode U) (encode V) (unitNormal S) (bas i) = mu i • bas i) :
    encode (numericalFlux g U V S) =
      (1 / 2 : ℝ) • (encode (physicalFlux g U S) + encode (physicalFlux g V S)) -
      (area S / 2) • bas.equivFun.symm
        (diagonal (fun i => |mu i|) (bas.equivFun (encode V - encode U))) := by
  classical
  unfold numericalFlux
  rw [encode_decode, roeFluxCoordinates, if_neg hS]
  rw [roe_absolute_basis g (encode U) (encode V) (unitNormal S) hg
    (by simpa only [decode_encode] using hU) (by simpa only [decode_encode] using hV)
    (unitNormal_dot_self S hS) bas mu he]
  simp only [coordinateFlux, decode_encode]
  rfl

-- Exact two-state intermediate is the same negative acoustic projector.
example : encode witnessIntermediate = encode witnessLeft +
    roeProjector 2 (encode witnessLeft) (encode witnessRight) ![1, 0, 0] 0
      (encode witnessRight - encode witnessLeft) := by
  unfold witnessIntermediate
  rw [encode_decode]
