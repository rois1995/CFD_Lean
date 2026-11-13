import CFDLean
import Integrity
import Lean
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

example (g : ℝ) (x y : StateCoordinates) (n : Vector 3) :
    dissipation g y x (-n) = dissipation g x y n := by
  rw [roe_absolute_reverse, (roe_swap g x y n).2.2]

example (g : ℝ) (x y : StateCoordinates) (n : Vector 3) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) (hn : dot n n = 1) :
    ∃ bas : Basis (Fin 5) ℝ StateCoordinates, ∃ mu : Fin 5 → ℝ,
      (∀ i, roeMatrix g x y n (bas i) = mu i • bas i) ∧
      dissipation g x y n = bas.equivFun.symm.toLinearMap.comp
        ((diagonal (fun i => |mu i|)).comp bas.equivFun.toLinearMap) := by
  classical
  obtain ⟨bas, hb⟩ := roe_complete_basis g x y n hg hx hy hn
  choose idx hi using hb
  let mu := fun i => roeSpeed g x y n (idx i)
  exact ⟨bas, mu, hi, roe_absolute_basis g x y n hg hx hy hn bas mu hi⟩
