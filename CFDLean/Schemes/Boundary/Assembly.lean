import CFDLean.Schemes.Boundary.Stationary

noncomputable section
namespace CFDLean.Boundary
open Coordinates
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

variable {N E B : Type*}

def constructedTransfer (m : Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind)
    (V : B → Conservative 3) (U : N → Conservative 3) (T : B → Vector 3) (b : B) : StateCoordinates :=
  transfer γ (k b) (U (m.owner b)) (V b) (T b)

theorem transfer_mass (γ : ℝ) (k : Kind) (U V : Conservative 3) (T : Vector 3) :
    transfer γ k U V T 0 = if k = .prescribedExteriorRoe then prescribedExteriorRoeTransfer γ U V T 0 else 0 := by
  cases k <;> rfl

theorem transfer_energy (γ : ℝ) (k : Kind) (U V : Conservative 3) (T : Vector 3) :
    transfer γ k U V T 4 = if k = .prescribedExteriorRoe then prescribedExteriorRoeTransfer γ U V T 4 else 0 := by
  cases k <;> rfl

theorem momentum_coordinate (f : StateCoordinates) (j : Fin 3) :
    (decode f).momentum j = f j.castSucc.succ := by
  fin_cases j <;> rfl

theorem transfer_momentum (γ : ℝ) (k : Kind) (U V : Conservative 3) (T : Vector 3) (j : Fin 3) :
    (decode (transfer γ k U V T)).momentum j = if k = .prescribedExteriorRoe then
      (decode (prescribedExteriorRoeTransfer γ U V T)).momentum j else U.pressure γ * T j := by
  cases k <;> simp [transfer, wall_momentum]

theorem transfer_split (γ : ℝ) (k : Kind) (U V : Conservative 3) (T : Vector 3) :
    transfer γ k U V T = (if k = .prescribedExteriorRoe then prescribedExteriorRoeTransfer γ U V T else 0) +
      (if k = .prescribedExteriorRoe then 0 else wallTransfer γ U T) := by
  cases k <;> simp [transfer]

theorem constructed_transfer_reindex {N' E' B' : Type*} (m : Assembly.Interfaces N E B)
    (n : N ≃ N') (e : E ≃ E') (b : B ≃ B') (γ : ℝ) (k : B → Kind)
    (V : B → Conservative 3) (U : N → Conservative 3) (T : B → Vector 3) (j : B') :
    constructedTransfer (m.reindex n e b) γ (fun x => k (b.symm x)) (fun x => V (b.symm x))
      (fun x => U (n.symm x)) (fun x => T (b.symm x)) j =
      constructedTransfer m γ k V U T (b.symm j) := by
  simp [constructedTransfer, Assembly.Interfaces.reindex]

variable [DecidableEq N] [Fintype E] [Fintype B]

/-- The accepted outgoing interior Roe residual with the selected, constructed boundary transfers. -/
def stationaryResidual (m : Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind)
    (V : B → Conservative 3) (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (i : N) : StateCoordinates :=
  Assembly.residual m (Assembly.roeTransfer m γ U S) (constructedTransfer m γ k V U T) i

theorem stationary_global_balance [Fintype N] (m : Assembly.Interfaces N E B) (γ : ℝ)
    (k : B → Kind) (V : B → Conservative 3) (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) :
    (∑ i, stationaryResidual m γ k V U S T i) = ∑ b, constructedTransfer m γ k V U T b :=
  Assembly.roe_global_balance m γ U S _

theorem stationary_mixed_balance [Fintype N] (m : Assembly.Interfaces N E B) (γ : ℝ)
    (k : B → Kind) (V : B → Conservative 3) (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) :
    (∑ i, stationaryResidual m γ k V U S T i) =
      (∑ b, if k b = .prescribedExteriorRoe then prescribedExteriorRoeTransfer γ (U (m.owner b)) (V b) (T b) else 0) +
      ∑ b, if k b = .prescribedExteriorRoe then 0 else wallTransfer γ (U (m.owner b)) (T b) := by
  rw [stationary_global_balance]
  simp only [constructedTransfer, transfer_split, Finset.sum_add_distrib]

theorem stationary_component_balance [Fintype N] (m : Assembly.Interfaces N E B) (γ : ℝ)
    (k : B → Kind) (V : B → Conservative 3) (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (j : Fin 5) :
    (∑ i, stationaryResidual m γ k V U S T i j) = ∑ b, constructedTransfer m γ k V U T b j := by
  simpa only [Finset.sum_apply] using congrFun (stationary_global_balance m γ k V U S T) j

theorem stationary_mass_balance [Fintype N] (m : Assembly.Interfaces N E B) (γ : ℝ)
    (k : B → Kind) (V : B → Conservative 3) (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) :
    (∑ i, stationaryResidual m γ k V U S T i 0) =
      ∑ b, if k b = .prescribedExteriorRoe then prescribedExteriorRoeTransfer γ (U (m.owner b)) (V b) (T b) 0 else 0 := by
  rw [stationary_component_balance]
  simp only [constructedTransfer, transfer_mass]

theorem stationary_energy_balance [Fintype N] (m : Assembly.Interfaces N E B) (γ : ℝ)
    (k : B → Kind) (V : B → Conservative 3) (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) :
    (∑ i, stationaryResidual m γ k V U S T i 4) =
      ∑ b, if k b = .prescribedExteriorRoe then prescribedExteriorRoeTransfer γ (U (m.owner b)) (V b) (T b) 4 else 0 := by
  rw [stationary_component_balance]
  simp only [constructedTransfer, transfer_energy]

theorem stationary_momentum_balance [Fintype N] (m : Assembly.Interfaces N E B) (γ : ℝ)
    (k : B → Kind) (V : B → Conservative 3) (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (j : Fin 3) :
    (∑ i, (decode (stationaryResidual m γ k V U S T i)).momentum j) =
      ∑ b, if k b = .prescribedExteriorRoe then
        (decode (prescribedExteriorRoeTransfer γ (U (m.owner b)) (V b) (T b))).momentum j
        else (U (m.owner b)).pressure γ * T b j := by
  simp only [momentum_coordinate]
  rw [stationary_component_balance]
  apply Finset.sum_congr rfl
  intro b _
  simpa only [momentum_coordinate, constructedTransfer] using transfer_momentum γ (k b) (U (m.owner b)) (V b) (T b) j

theorem stationary_residual_reindex {N' E' B' : Type*} [DecidableEq N'] [Fintype E'] [Fintype B']
    (m : Assembly.Interfaces N E B) (n : N ≃ N') (e : E ≃ E') (b : B ≃ B') (γ : ℝ)
    (k : B → Kind) (V : B → Conservative 3) (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (i : N) :
    stationaryResidual (m.reindex n e b) γ (fun x => k (b.symm x)) (fun x => V (b.symm x))
      (fun x => U (n.symm x)) (fun x => S (e.symm x)) (fun x => T (b.symm x)) (n i) =
      stationaryResidual m γ k V U S T i := by
  unfold stationaryResidual
  have hg : constructedTransfer (m.reindex n e b) γ (fun x => k (b.symm x)) (fun x => V (b.symm x))
      (fun x => U (n.symm x)) (fun x => T (b.symm x)) = fun x => constructedTransfer m γ k V U T (b.symm x) := by
    funext j
    exact constructed_transfer_reindex m n e b γ k V U T j
  rw [hg]
  exact Assembly.roe_residual_reindex m n e b γ U S _ i

omit [DecidableEq N] [Fintype E] [Fintype B] in
theorem transfer_compatible (γ : ℝ) (k : Kind) (U V : Conservative 3) (T : Vector 3)
    (hWall : k ≠ .prescribedExteriorRoe → dot U.momentum T = 0)
    (hMatch : k = .prescribedExteriorRoe → V = U) :
    transfer γ k U V T = Assembly.physicalTransfer γ U T := by
  cases k with
  | slipWall => exact (wall_eq_physical_iff γ U T).mpr (hWall (by decide))
  | inviscidSymmetryTraction => exact (wall_eq_physical_iff γ U T).mpr (hWall (by decide))
  | prescribedExteriorRoe =>
    simp only [transfer, hMatch rfl]
    exact prescribed_consistency γ U T

theorem stationary_common_defect (m : Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind)
    (V : B → Conservative 3) (U : Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (i : N)
    (hWall : ∀ b, k b ≠ .prescribedExteriorRoe → dot U.momentum (T b) = 0)
    (hMatch : ∀ b, k b = .prescribedExteriorRoe → V b = U) :
    stationaryResidual m γ k V (fun _ => U) S T i = encode (physicalFlux γ U (Assembly.metricDefect m S T i)) := by
  have hg : constructedTransfer m γ k V (fun _ => U) T = fun b => Assembly.physicalTransfer γ U (T b) := by
    funext b
    exact transfer_compatible γ (k b) U (V b) (T b) (hWall b) (hMatch b)
  unfold stationaryResidual
  rw [hg]
  exact Assembly.constant_state_residual m γ U S T i

theorem stationary_common_closed (m : Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind)
    (V : B → Conservative 3) (U : Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (i : N)
    (hWall : ∀ b, k b ≠ .prescribedExteriorRoe → dot U.momentum (T b) = 0)
    (hMatch : ∀ b, k b = .prescribedExteriorRoe → V b = U)
    (hMetric : Assembly.metricDefect m S T i = 0) : stationaryResidual m γ k V (fun _ => U) S T i = 0 := by
  rw [stationary_common_defect m γ k V U S T i hWall hMatch, hMetric]
  exact (Assembly.physicalTransfer γ U).map_zero

theorem residual_boundary_difference (m : Assembly.Interfaces N E B) (f : E → StateCoordinates)
    (g h : B → StateCoordinates) (i : N) : Assembly.residual m f g i = Assembly.residual m f h i +
      ∑ b, if m.owner b = i then g b - h b else 0 := by
  unfold Assembly.residual
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  by_cases ho : m.owner b = i
  · simp only [ite_eq_left ho]
    module
  · simp [ho]

theorem stationary_common_correction (m : Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind)
    (V : B → Conservative 3) (U : Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (i : N) :
    stationaryResidual m γ k V (fun _ => U) S T i = encode (physicalFlux γ U (Assembly.metricDefect m S T i)) +
      ∑ b, if m.owner b = i then constructedTransfer m γ k V (fun _ => U) T b - Assembly.physicalTransfer γ U (T b) else 0 := by
  unfold stationaryResidual
  rw [residual_boundary_difference m _ _ (fun b => Assembly.physicalTransfer γ U (T b)) i]
  rw [Assembly.constant_state_residual]

/-- The concrete residual uses the exact already accepted patchTransfer and edge Roe transfer. -/
def meshResidual {n m : ℕ} (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (i : Fin n) : StateCoordinates :=
  stationaryResidual M.interfaces γ (patchKind M k) (patchExterior M V) U M.edgeArea M.boundaryArea i

theorem meshResidual_eq {n m : ℕ} (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (i : Fin n) :
    meshResidual M γ k V U i = Assembly.residual M.interfaces (Assembly.roeTransfer M.interfaces γ U M.edgeArea)
      (patchTransfer M γ k V U) i := rfl

theorem mesh_global_balance {n m : ℕ} (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) :
    (∑ i, meshResidual M γ k V U i) = ∑ b, patchTransfer M γ k V U b :=
  stationary_global_balance M.interfaces γ (patchKind M k) (patchExterior M V) U M.edgeArea M.boundaryArea

theorem mesh_residual_reindex {n m : ℕ} {N' E' B' : Type*} [DecidableEq N'] [Fintype E'] [Fintype B']
    (M : MedianDual.MeshData n m) (nodeEq : Fin n ≃ N') (e : M.Edge ≃ E') (b : M.Boundary ≃ B') (γ : ℝ)
    (k : Finset (Fin n) → Kind) (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (i : Fin n) :
    stationaryResidual (M.interfaces.reindex nodeEq e b) γ (fun x => patchKind M k (b.symm x))
      (fun x => patchExterior M V (b.symm x)) (fun x => U (nodeEq.symm x))
      (fun x => M.edgeArea (e.symm x)) (fun x => M.boundaryArea (b.symm x)) (nodeEq i) =
      meshResidual M γ k V U i := stationary_residual_reindex M.interfaces nodeEq e b γ _ _ U _ _ i

theorem mesh_constant_state {n m : ℕ} (M : MedianDual.MeshData n m) (hM : M.Conforming) (γ : ℝ)
    (_hγ : 1 < γ) (U : Conservative 3) (_hU : U.Admissible γ) (k : Finset (Fin n) → Kind)
    (V : Finset (Fin n) → Conservative 3) (i : Fin n)
    (hWall : ∀ b : M.Boundary, patchKind M k b ≠ .prescribedExteriorRoe → dot U.momentum (M.boundaryArea b) = 0)
    (hMatch : ∀ b : M.Boundary, patchKind M k b = .prescribedExteriorRoe → patchExterior M V b = U) :
    meshResidual M γ k V (fun _ => U) i = 0 :=
  stationary_common_closed M.interfaces γ (patchKind M k) (patchExterior M V) U M.edgeArea M.boundaryArea i hWall hMatch (M.metric_closed hM i)

theorem mesh_common_correction {n m : ℕ} (M : MedianDual.MeshData n m) (hM : M.Conforming) (γ : ℝ)
    (k : Finset (Fin n) → Kind) (V : Finset (Fin n) → Conservative 3) (U : Conservative 3) (i : Fin n) :
    meshResidual M γ k V (fun _ => U) i =
      ∑ b : M.Boundary, if M.interfaces.owner b = i then
        patchTransfer M γ k V (fun _ => U) b - Assembly.physicalTransfer γ U (M.boundaryArea b) else 0 := by
  unfold meshResidual
  rw [stationary_common_correction, M.metric_closed hM i]
  have hz : encode (physicalFlux γ U (0 : Vector 3)) = 0 := (Assembly.physicalTransfer γ U).map_zero
  rw [hz, zero_add]
  rfl

end CFDLean.Boundary
