import CFDLean
import Integrity
import Lean
open Lean CFDLean Coordinates PhysicalJacobian Roe

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

open CFDLean.Assembly
open scoped BigOperators

example {N E B : Type*} [Fintype N] [Fintype E] [Fintype B] [DecidableEq N]
    (m : Interfaces N E B) (g : ℝ) (U : N → Conservative 3) (S : E → Vector 3)
    (out : B → StateCoordinates) :
    (∑ i, ((∑ e, outwardTransfer m g U S i e) +
      ∑ b, if m.owner b = i then out b else 0)) = ∑ b, out b := by
  simp_rw [outwardTransfer_eq]
  exact roe_global_balance m g U S out

example {N E B : Type*} [Fintype E] [Fintype B] [DecidableEq N]
    (m : Interfaces N E B) (g : ℝ) (U : Conservative 3)
    (S : E → Vector 3) (T : B → Vector 3) (out : B → StateCoordinates)
    (h : ∀ b, out b = encode (physicalFlux g U (T b))) (i : N) :
    residual m (roeTransfer m g (fun _ => U) S) out i =
      encode (physicalFlux g U (metricDefect m S T i)) := by
  have ho : out = fun b => physicalTransfer g U (T b) := funext h
  rw [ho]
  exact constant_state_residual m g U S T i

open CFDLean.MedianDual
example {n m : ℕ} (M : MeshData n m) (t : Fin m) (i j k l : Fin 4)
    (h : valid i j k l) :
    0 < dot (outwardTriangle (M.points t) i j k l) (M.points t j - M.points t i) := by
  rw [outwardTriangle_dot _ _ _ _ _ h]
  exact div_pos (M.positive t) (by norm_num)

example {n m : ℕ} (M : MeshData n m) (h : M.Conforming) (g : ℝ) (U : Conservative 3)
    (_hg : 1 < g) (_hu : U.Admissible g) :
    (∀ i, Assembly.residual M.interfaces (Assembly.roeTransfer M.interfaces g (fun _ => U) M.edgeArea)
      (fun b => Assembly.physicalTransfer g U (M.boundaryArea b)) i = 0) ∧
    (∀ i, M.Used i → 0 < M.dualVolume i) ∧
    (∑ i, M.dualVolume i) = ∑ t, volume (M.points t) := by
  exact ⟨fun i => M.constant_state h g U i, fun i hi => M.dualVolume_pos i hi, M.volume_partition h⟩

example : encode (numericalFlux 2 (decode RoeAggregation.cold) (decode RoeAggregation.hot) ![1,1,0]) ≠
    encode (numericalFlux 2 (decode RoeAggregation.cold) (decode RoeAggregation.hot) ![1,0,0]) +
    encode (numericalFlux 2 (decode RoeAggregation.cold) (decode RoeAggregation.hot) ![0,1,0]) := by
  simp only [numericalFlux, encode_decode]
  exact RoeAggregation.nonparallel_not_additive

open CFDLean.Boundary
example (g : ℝ) (k : CFDLean.Boundary.Kind) (U : Conservative 3) (T : Vector 3)
    (h : dot U.momentum T = 0) :
    transfer g k U U T = encode (physicalFlux g U T) := by
  cases k
  · exact (wall_eq_physical_iff g U T).mpr h
  · exact (wall_eq_physical_iff g U T).mpr h
  · exact prescribed_consistency g U T

example {n m : ℕ} (M : MedianDual.MeshData n m) (g : ℝ)
    (k : Finset (Fin n) → CFDLean.Boundary.Kind) (U : Fin n → Conservative 3)
    (V V' : Finset (Fin n) → Conservative 3) (b : M.Boundary)
    (h : patchKind M k b = .slipWall) :
    patchTransfer M g k V U b = patchTransfer M g k V' U b := by
  rw [patchTransfer_wall M g k V U b h, patchTransfer_wall M g k V' U b h]

example {n m : ℕ} (M : MedianDual.MeshData n m) (hM : M.Conforming)
    (g : ℝ) (hg : 1 < g) (U : Conservative 3) (hU : U.Admissible g)
    (k : Finset (Fin n) → CFDLean.Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3)
    (hw : ∀ b : M.Boundary, patchKind M k b ≠ .prescribedExteriorRoe → dot U.momentum (M.boundaryArea b) = 0)
    (hv : ∀ b : M.Boundary, patchKind M k b = .prescribedExteriorRoe → patchExterior M V b = U) :
    (∀ i, meshResidual M g k V (fun _ => U) i = 0) ∧
    (∀ i, M.Used i → 0 < M.dualVolume i) := by
  exact ⟨fun i => mesh_constant_state M hM g hg U hU k V i hw hv,
    fun i hi => M.dualVolume_pos i hi⟩

example {N E B : Type*} [DecidableEq N] [Fintype E] [Fintype B]
    (iF : Assembly.Interfaces N E B) (g : ℝ) (U : Conservative 3)
    (k : B → CFDLean.Boundary.Kind) (V : B → Conservative 3)
    (S : E → Vector 3) (T : B → Vector 3) (i : N) :
    stationaryResidual iF g k V (fun _ => U) S T i -
      encode (physicalFlux g U (Assembly.metricDefect iF S T i)) =
      ∑ b, if iF.owner b = i then constructedTransfer iF g k V (fun _ => U) T b -
        Assembly.physicalTransfer g U (T b) else 0 := by
  rw [stationary_common_correction]
  module
