import CFDLean.Boundary.Assembly

noncomputable section
namespace CFDLean.Time
open Coordinates
open scoped BigOperators

/-- One correction of the selected lumped fixed-volume ODE, at the old state. -/
def euler (v τ : ℝ) (R : StateCoordinates) (U : Conservative 3) : Conservative 3 :=
  decode (encode U - (τ / v) • R)

theorem euler_coordinates (v τ : ℝ) (R : StateCoordinates) (U : Conservative 3) :
    encode (euler v τ R U) = encode U - (τ / v) • R := encode_decode _

theorem euler_zero_step (v : ℝ) (R : StateCoordinates) (U : Conservative 3) : euler v 0 R U = U := by
  simp [euler, decode_encode]

theorem euler_zero_residual (v τ : ℝ) (U : Conservative 3) : euler v τ 0 U = U := by
  simp [euler, decode_encode]

theorem euler_amount (v τ : ℝ) (hv : v ≠ 0) (R : StateCoordinates) (U : Conservative 3) :
    v • encode (euler v τ R U) = v • encode U - τ • R := by
  rw [euler_coordinates, smul_sub, smul_smul]
  have hc : v * (τ / v) = τ := by field_simp
  rw [hc]

variable {N : Type*}

/-- The unused branch returns its old value without evaluating a volume quotient. -/
def heldStep (used : N → Prop) (v τ : N → ℝ) (R : N → StateCoordinates)
    (U : N → Conservative 3) (i : N) : Conservative 3 := by
  classical
  exact if used i then euler (v i) (τ i) (R i) (U i) else U i

theorem held_unused (used : N → Prop) (v τ : N → ℝ) (R : N → StateCoordinates)
    (U : N → Conservative 3) (i : N) (hi : ¬used i) : heldStep used v τ R U i = U i := by
  simp [heldStep, hi]

theorem held_zero_residual (used : N → Prop) (v τ : N → ℝ) (U : N → Conservative 3) (i : N) :
    heldStep used v τ (fun _ => 0) U i = U i := by
  classical
  by_cases hi : used i <;> simp [heldStep, hi, euler_zero_residual]

def amount [Fintype N] (v : N → ℝ) (U : N → Conservative 3) : StateCoordinates :=
  ∑ i, v i • encode (U i)

theorem held_amount [Fintype N] (used : N → Prop) (v τ : N → ℝ) (R : N → StateCoordinates)
    (U : N → Conservative 3) (hv : ∀ i, used i → v i ≠ 0) (hR : ∀ i, ¬used i → R i = 0) :
    amount v (heldStep used v τ R U) = amount v U - ∑ i, τ i • R i := by
  classical
  have hi (i : N) : v i • encode (heldStep used v τ R U i) = v i • encode (U i) - τ i • R i := by
    by_cases h : used i
    · simpa only [heldStep, ite_eq_left h] using euler_amount (v i) (τ i) (hv i h) (R i) (U i)
    · simp [heldStep, h, hR i h]
  simp only [amount, hi, Finset.sum_sub_distrib]

open Classical in
theorem amount_used [Fintype N] (used : N → Prop) (v : N → ℝ) (U : N → Conservative 3)
    (hv : ∀ i, ¬used i → v i = 0) :
    amount v U = ∑ i ∈ Finset.univ.filter used, v i • encode (U i) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : used i <;> simp [h, hv i]

theorem held_reindex {N' : Type*} (n : N ≃ N') (used : N → Prop) (v τ : N → ℝ)
    (R : N → StateCoordinates) (U : N → Conservative 3) (i : N) :
    heldStep (fun x => used (n.symm x)) (fun x => v (n.symm x)) (fun x => τ (n.symm x))
      (fun x => R (n.symm x)) (fun x => U (n.symm x)) (n i) = heldStep used v τ R U i := by
  change heldStep used v τ R U (n.symm (n i)) = heldStep used v τ R U i
  exact congrArg (heldStep used v τ R U) (n.symm_apply_apply i)

theorem amount_reindex {N' : Type*} [Fintype N] [Fintype N'] (n : N ≃ N')
    (v : N → ℝ) (U : N → Conservative 3) :
    amount (fun x => v (n.symm x)) (fun x => U (n.symm x)) = amount v U := by
  apply Fintype.sum_equiv n.symm
  intro i
  rfl

variable {E B : Type*} [DecidableEq N] [Fintype N] [Fintype E] [Fintype B]

theorem weighted_residual (m : Assembly.Interfaces N E B) (τ : N → ℝ)
    (f : E → StateCoordinates) (g : B → StateCoordinates) :
    (∑ i, τ i • Assembly.residual m f g i) =
      (∑ e, (τ (m.tail e) - τ (m.head e)) • f e) + ∑ b, τ (m.owner b) • g b := by
  classical
  simp only [Assembly.residual, smul_add, Finset.smul_sum, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp [Assembly.incidence_smul, smul_sub, smul_ite, ← sub_smul, Finset.sum_sub_distrib]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    simp [smul_ite]

variable {n m : ℕ}

theorem tail_used (M : MedianDual.MeshData n m) (e : M.Edge) : M.Used (M.interfaces.tail e) := by
  obtain ⟨t, ht, _⟩ := e.prop.2
  obtain ⟨i, hi⟩ := (M.mem_cellNodes t _).mp ht
  exact ⟨t, i, hi⟩

theorem head_used (M : MedianDual.MeshData n m) (e : M.Edge) : M.Used (M.interfaces.head e) := by
  obtain ⟨t, _, ht⟩ := e.prop.2
  obtain ⟨i, hi⟩ := (M.mem_cellNodes t _).mp ht
  exact ⟨t, i, hi⟩

theorem owner_used (M : MedianDual.MeshData n m) (b : M.Boundary) : M.Used (M.interfaces.owner b) := by
  obtain ⟨i, _, hi⟩ := (M.mem_faceNodes b.1.1.1 b.1.1.2 _).mp b.prop.2
  exact ⟨b.1.1.1, i, hi⟩

theorem mesh_residual_unused (M : MedianDual.MeshData n m) (γ : ℝ)
    (k : Finset (Fin n) → Boundary.Kind) (V : Finset (Fin n) → Conservative 3)
    (U : Fin n → Conservative 3) (i : Fin n) (hi : ¬M.Used i) : Boundary.meshResidual M γ k V U i = 0 := by
  rw [Boundary.meshResidual_eq]
  unfold Assembly.residual
  have ht (e : M.Edge) : M.interfaces.tail e ≠ i := fun h => hi (h ▸ tail_used M e)
  have hh (e : M.Edge) : M.interfaces.head e ≠ i := fun h => hi (h ▸ head_used M e)
  have hb (b : M.Boundary) : M.interfaces.owner b ≠ i := fun h => hi (h ▸ owner_used M b)
  simp [Assembly.incidence, ht, hh, hb]

def meshStep (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (τ : Fin n → ℝ) (U : Fin n → Conservative 3) : Fin n → Conservative 3 :=
  heldStep M.Used M.dualVolume τ (Boundary.meshResidual M γ k V U) U

theorem mesh_step_used (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (τ : Fin n → ℝ) (U : Fin n → Conservative 3)
    (i : Fin n) (hi : M.Used i) : meshStep M γ k V τ U i =
      decode (encode (U i) - (τ i / M.dualVolume i) • Boundary.meshResidual M γ k V U i) := by
  simp [meshStep, heldStep, hi, euler]

theorem mesh_used_volume_pos (M : MedianDual.MeshData n m) (i : Fin n) (hi : M.Used i) :
    0 < M.dualVolume i := M.dualVolume_pos i hi

theorem mesh_point_amount (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (τ : Fin n → ℝ) (U : Fin n → Conservative 3)
    (i : Fin n) (hi : M.Used i) :
    M.dualVolume i • encode (meshStep M γ k V τ U i) = M.dualVolume i • encode (U i) -
      τ i • Boundary.meshResidual M γ k V U i := by
  rw [mesh_step_used _ _ _ _ _ _ i hi]
  exact euler_amount _ _ (ne_of_gt (M.dualVolume_pos i hi)) _ _

theorem mesh_zero_step (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (i : Fin n) :
    meshStep M γ k V (fun _ => 0) U i = U i := by
  classical
  by_cases hi : M.Used i <;> simp [meshStep, heldStep, hi, euler_zero_step]


theorem mesh_step_unused (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (τ : Fin n → ℝ) (U : Fin n → Conservative 3)
    (i : Fin n) (hi : ¬M.Used i) : meshStep M γ k V τ U i = U i := held_unused _ _ _ _ _ i hi

open Classical in
theorem mesh_amount_used (M : MedianDual.MeshData n m) (U : Fin n → Conservative 3) :
    amount M.dualVolume U = ∑ i ∈ Finset.univ.filter M.Used, M.dualVolume i • encode (U i) :=
  amount_used M.Used M.dualVolume U M.dualVolume_unused

theorem mesh_amount_change (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (τ : Fin n → ℝ) (U : Fin n → Conservative 3) :
    amount M.dualVolume (meshStep M γ k V τ U) = amount M.dualVolume U -
      ∑ i, τ i • Boundary.meshResidual M γ k V U i :=
  held_amount M.Used M.dualVolume τ _ U (fun i hi => ne_of_gt (M.dualVolume_pos i hi)) (mesh_residual_unused M γ k V U)

theorem mesh_common_balance (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (τ : Fin n → ℝ) (U : Fin n → Conservative 3) (dt : ℝ)
    (hτ : ∀ i, M.Used i → τ i = dt) :
    amount M.dualVolume (meshStep M γ k V τ U) = amount M.dualVolume U -
      dt • ∑ b, Boundary.patchTransfer M γ k V U b := by
  rw [mesh_amount_change]
  have hs : (∑ i, τ i • Boundary.meshResidual M γ k V U i) = dt • ∑ i, Boundary.meshResidual M γ k V U i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : M.Used i
    · rw [hτ i hi]
    · rw [mesh_residual_unused M γ k V U i hi, smul_zero, smul_zero]
  rw [hs, Boundary.mesh_global_balance]

theorem mesh_common_balance_physical (M : MedianDual.MeshData n m) (γ : ℝ) (_hγ : 1 < γ)
    (k : Finset (Fin n) → Boundary.Kind) (V : Finset (Fin n) → Conservative 3)
    (τ : Fin n → ℝ) (U : Fin n → Conservative 3) (dt : ℝ) (_hdt : 0 ≤ dt)
    (_hU : ∀ i, M.Used i → (U i).Admissible γ)
    (_hV : ∀ b : M.Boundary, Boundary.patchKind M k b = .prescribedExteriorRoe → (Boundary.patchExterior M V b).Admissible γ)
    (hτ : ∀ i, M.Used i → τ i = dt) :
    amount M.dualVolume (meshStep M γ k V τ U) = amount M.dualVolume U -
      dt • ∑ b, Boundary.patchTransfer M γ k V U b := mesh_common_balance M γ k V τ U dt hτ

theorem mesh_component_balance (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (dt : ℝ) (j : Fin 5) :
    (∑ i, M.dualVolume i * encode (meshStep M γ k V (fun _ => dt) U i) j) =
      (∑ i, M.dualVolume i * encode (U i) j) - dt * ∑ b, Boundary.patchTransfer M γ k V U b j := by
  simpa only [amount, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
    congrFun (mesh_common_balance M γ k V (fun _ => dt) U dt (fun _ _ => rfl)) j

theorem mesh_mass_balance (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (dt : ℝ) :
    (∑ i, M.dualVolume i * (meshStep M γ k V (fun _ => dt) U i).density) =
      (∑ i, M.dualVolume i * (U i).density) - dt * ∑ b,
        if Boundary.patchKind M k b = .prescribedExteriorRoe then
          Boundary.prescribedExteriorRoeTransfer γ (U (M.interfaces.owner b)) (Boundary.patchExterior M V b) (M.boundaryArea b) 0 else 0 := by
  simpa only [encode, Matrix.cons_val_zero, Boundary.patchTransfer, Boundary.transfer_mass] using
    mesh_component_balance M γ k V U dt 0

theorem mesh_energy_balance (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (dt : ℝ) :
    (∑ i, M.dualVolume i * (meshStep M γ k V (fun _ => dt) U i).energy) =
      (∑ i, M.dualVolume i * (U i).energy) - dt * ∑ b,
        if Boundary.patchKind M k b = .prescribedExteriorRoe then
          Boundary.prescribedExteriorRoeTransfer γ (U (M.interfaces.owner b)) (Boundary.patchExterior M V b) (M.boundaryArea b) 4 else 0 := by
  have h := mesh_component_balance M γ k V U dt 4
  simp only [Boundary.patchTransfer, Boundary.transfer_energy] at h
  exact h

theorem encode_momentum (U : Conservative 3) (j : Fin 3) : encode U j.castSucc.succ = U.momentum j := by
  fin_cases j <;> rfl

theorem mesh_momentum_balance (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (dt : ℝ) (j : Fin 3) :
    (∑ i, M.dualVolume i * (meshStep M γ k V (fun _ => dt) U i).momentum j) =
      (∑ i, M.dualVolume i * (U i).momentum j) - dt * ∑ b,
        if Boundary.patchKind M k b = .prescribedExteriorRoe then
          (decode (Boundary.prescribedExteriorRoeTransfer γ (U (M.interfaces.owner b)) (Boundary.patchExterior M V b) (M.boundaryArea b))).momentum j
        else (U (M.interfaces.owner b)).pressure γ * M.boundaryArea b j := by
  have h := mesh_component_balance M γ k V U dt j.castSucc.succ
  simp only [encode_momentum] at h
  rw [h]
  congr 2
  apply Finset.sum_congr rfl
  intro b _
  exact (Boundary.momentum_coordinate _ j).symm.trans (Boundary.transfer_momentum γ _ _ _ _ j)

theorem mesh_local_balance (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (τ : Fin n → ℝ) (U : Fin n → Conservative 3) :
    amount M.dualVolume (meshStep M γ k V τ U) = amount M.dualVolume U -
      ((∑ e : M.Edge, (τ (M.interfaces.tail e) - τ (M.interfaces.head e)) • Assembly.roeTransfer M.interfaces γ U M.edgeArea e) +
       ∑ b : M.Boundary, τ (M.interfaces.owner b) • Boundary.patchTransfer M γ k V U b) := by
  rw [mesh_amount_change]
  simp_rw [Boundary.meshResidual_eq]
  rw [weighted_residual]

theorem mesh_local_balance_physical (M : MedianDual.MeshData n m) (γ : ℝ) (_hγ : 1 < γ)
    (k : Finset (Fin n) → Boundary.Kind) (V : Finset (Fin n) → Conservative 3)
    (τ : Fin n → ℝ) (_hτ : ∀ i, M.Used i → 0 ≤ τ i) (U : Fin n → Conservative 3)
    (_hU : ∀ i, M.Used i → (U i).Admissible γ)
    (_hV : ∀ b : M.Boundary, Boundary.patchKind M k b = .prescribedExteriorRoe → (Boundary.patchExterior M V b).Admissible γ) :
    amount M.dualVolume (meshStep M γ k V τ U) = amount M.dualVolume U -
      ((∑ e : M.Edge, (τ (M.interfaces.tail e) - τ (M.interfaces.head e)) • Assembly.roeTransfer M.interfaces γ U M.edgeArea e) +
       ∑ b : M.Boundary, τ (M.interfaces.owner b) • Boundary.patchTransfer M γ k V U b) := mesh_local_balance M γ k V τ U

theorem mesh_traction_mass (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (dt : ℝ)
    (hk : ∀ b : M.Boundary, Boundary.patchKind M k b ≠ .prescribedExteriorRoe) :
    (∑ i, M.dualVolume i * (meshStep M γ k V (fun _ => dt) U i).density) = ∑ i, M.dualVolume i * (U i).density := by
  rw [mesh_mass_balance]
  simp [hk]

theorem mesh_traction_energy (M : MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Boundary.Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (dt : ℝ)
    (hk : ∀ b : M.Boundary, Boundary.patchKind M k b ≠ .prescribedExteriorRoe) :
    (∑ i, M.dualVolume i * (meshStep M γ k V (fun _ => dt) U i).energy) = ∑ i, M.dualVolume i * (U i).energy := by
  rw [mesh_energy_balance]
  simp [hk]


theorem mesh_common_state (M : MedianDual.MeshData n m) (hM : M.Conforming) (γ : ℝ) (hγ : 1 < γ)
    (k : Finset (Fin n) → Boundary.Kind) (V : Finset (Fin n) → Conservative 3)
    (τ : Fin n → ℝ) (_hτ : ∀ i, M.Used i → 0 ≤ τ i) (U : Conservative 3) (hU : U.Admissible γ)
    (hWall : ∀ b : M.Boundary, Boundary.patchKind M k b ≠ .prescribedExteriorRoe → dot U.momentum (M.boundaryArea b) = 0)
    (hMatch : ∀ b : M.Boundary, Boundary.patchKind M k b = .prescribedExteriorRoe → Boundary.patchExterior M V b = U)
    (i : Fin n) : meshStep M γ k V τ (fun _ => U) i = U := by
  have hr : Boundary.meshResidual M γ k V (fun _ => U) = fun _ => 0 := by
    funext a
    exact Boundary.mesh_constant_state M hM γ hγ U hU k V a hWall hMatch
  unfold meshStep
  rw [hr]
  exact held_zero_residual _ _ _ _ i

theorem mesh_step_reindex {N' E' B' : Type*} [DecidableEq N'] [Fintype E'] [Fintype B']
    (M : MedianDual.MeshData n m) (nodeEq : Fin n ≃ N') (e : M.Edge ≃ E') (b : M.Boundary ≃ B') (γ : ℝ)
    (k : Finset (Fin n) → Boundary.Kind) (V : Finset (Fin n) → Conservative 3)
    (τ : Fin n → ℝ) (U : Fin n → Conservative 3) (i : Fin n) :
    heldStep (fun x => M.Used (nodeEq.symm x)) (fun x => M.dualVolume (nodeEq.symm x)) (fun x => τ (nodeEq.symm x))
      (Boundary.stationaryResidual (M.interfaces.reindex nodeEq e b) γ
        (fun x => Boundary.patchKind M k (b.symm x)) (fun x => Boundary.patchExterior M V (b.symm x))
        (fun x => U (nodeEq.symm x)) (fun x => M.edgeArea (e.symm x)) (fun x => M.boundaryArea (b.symm x)))
      (fun x => U (nodeEq.symm x)) (nodeEq i) = meshStep M γ k V τ U i := by
  have hr : Boundary.stationaryResidual (M.interfaces.reindex nodeEq e b) γ
        (fun x => Boundary.patchKind M k (b.symm x)) (fun x => Boundary.patchExterior M V (b.symm x))
        (fun x => U (nodeEq.symm x)) (fun x => M.edgeArea (e.symm x)) (fun x => M.boundaryArea (b.symm x)) =
      fun x => Boundary.meshResidual M γ k V U (nodeEq.symm x) := by
    funext x
    simpa only [Equiv.apply_symm_apply] using Boundary.mesh_residual_reindex M nodeEq e b γ k V U (nodeEq.symm x)
  rw [hr]
  exact held_reindex nodeEq _ _ _ _ _ i

end CFDLean.Time
