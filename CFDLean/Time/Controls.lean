import CFDLean.Time.ExplicitEuler
import CFDLean.Boundary.AssemblyControls

noncomputable section
namespace CFDLean.Time.Controls
open Coordinates Boundary Roe PhysicalJacobian
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
attribute [local irreducible] Spectral.shift Spectral.b Spectral.dp Spectral.minus Spectral.plus Spectral.zero
abbrev standard := MedianDual.Controls.standard
abbrev moving := Boundary.Controls.moving
abbrev normalState := Boundary.AssemblyControls.normalState

def wallLinear (γ : ℝ) (U : Conservative 3) : Vector 3 →ₗ[ℝ] StateCoordinates where
  toFun := wallTransfer γ U
  map_add' := wall_add γ U
  map_smul' a T := wall_smul γ a U T

theorem all_wall_common_residual {n m : ℕ} (M : MedianDual.MeshData n m) (hM : M.Conforming)
    (γ : ℝ) (U : Conservative 3) (V : Finset (Fin n) → Conservative 3) (i : Fin n) :
    meshResidual M γ (fun _ => .slipWall) V (fun _ => U) i =
      (wallLinear γ U - Assembly.physicalTransfer γ U) (∑ b : M.Boundary, if M.interfaces.owner b = i then M.boundaryArea b else 0) := by
  rw [mesh_common_correction M hM, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hi : M.interfaces.owner b = i <;>
    simp [hi, patchTransfer, patchKind, transfer, wallLinear, wall_zero]

def boundaryTotals : Fin 4 → Vector 3 := ![![-1/6,-1/6,-1/6], ![1/6,0,0], ![0,1/6,0], ![0,0,1/6]]

theorem standard_boundary_total (i : Fin 4) :
    (∑ b : standard.Boundary, if standard.interfaces.owner b = i then standard.boundaryArea b else 0) = boundaryTotals i := by
  change (∑ b : standard.Boundary, if b.1.2 = i then standard.boundaryArea b else 0) = _
  rw [standard.boundary_sum]
  have hc (o : standard.Occurrence) : standard.faceCount (standard.faceID o) = 1 := by
    obtain ⟨t,j⟩ := o
    fin_cases t
    fin_cases j <;> decide
  simp only [hc, ite_true]
  rw [Fintype.sum_prod_type]
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_one, Fin.sum_univ_four, MedianDual.MeshData.ownedPatch,
      MedianDual.MeshData.faceID, MedianDual.MeshData.faceNodes, MedianDual.MeshData.faceArea,
      MedianDual.MeshData.points, MedianDual.Controls.standard, MedianDual.Controls.oneCell,
      MedianDual.Controls.standardPoints, MedianDual.faceVector, MedianDual.triangle, MedianDual.cross, boundaryTotals]

def r : StateCoordinates := ![1/6,0,0,1/6,5/12]

theorem all_wall_residual (i : Fin 4) : meshResidual standard 2 (fun _ => .slipWall)
    (fun _ => normalState) (fun _ => normalState) i = ![r,0,0,-r] i := by
  rw [all_wall_common_residual standard MedianDual.Controls.standard_conforming, standard_boundary_total]
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [wallLinear, wallTransfer, pressureTransfer, Assembly.physicalTransfer, physicalFlux,
      Boundary.AssemblyControls.normalState, Conservative.pressure, encode, dot_three, squareSum_three, boundaryTotals, r]

theorem standard_used (i : Fin 4) : standard.Used i := ⟨0,i,rfl⟩

def localSteps : Fin 4 → ℝ := ![1/48,1/48,1/48,1/24]

theorem local_steps_nonneg (i : Fin 4) : 0 ≤ localSteps i := by fin_cases i <;> norm_num [localSteps]

theorem local_amount_change :
    amount standard.dualVolume (meshStep standard 2 (fun _ => .slipWall) (fun _ => normalState) localSteps (fun _ => normalState)) =
      amount standard.dualVolume (fun _ => normalState) + ![1/288,0,0,1/288,5/576] := by
  rw [mesh_amount_change]
  simp_rw [all_wall_residual]
  ext j
  fin_cases j <;> norm_num [Fin.sum_univ_four, localSteps, r, Fin.ext_iff]

theorem local_nonconservation :
    amount standard.dualVolume (meshStep standard 2 (fun _ => .slipWall) (fun _ => normalState) localSteps (fun _ => normalState)) ≠
      amount standard.dualVolume (fun _ => normalState) := by
  rw [local_amount_change]
  intro h
  have h0 := congrFun h 0
  simp only [Pi.add_apply, Matrix.cons_val_zero] at h0
  linarith


theorem local_updated_admissible (i : Fin 4) :
    (meshStep standard 2 (fun _ => .slipWall) (fun _ => normalState) localSteps (fun _ => normalState) i).Admissible 2 := by
  rw [mesh_step_used _ _ _ _ _ _ i (standard_used i), MedianDual.Controls.standard_volume, all_wall_residual]
  fin_cases i <;> norm_num [localSteps, Fin.ext_iff, r, decode, encode, Boundary.AssemblyControls.normalState,
    Conservative.Admissible, Conservative.pressure, squareSum_three]

theorem all_wall_boundary_zero :
    (∑ b : standard.Boundary, patchTransfer standard 2 (fun _ => .slipWall) (fun _ => normalState) (fun _ => normalState) b) = 0 := by
  rw [← mesh_global_balance]
  simp_rw [all_wall_residual]
  simp [Fin.sum_univ_four]

theorem common_amount (dt : ℝ) :
    amount standard.dualVolume (meshStep standard 2 (fun _ => .slipWall) (fun _ => normalState) (fun _ => dt) (fun _ => normalState)) =
      amount standard.dualVolume (fun _ => normalState) := by
  rw [mesh_common_balance _ _ _ _ _ _ dt (fun _ _ => rfl), all_wall_boundary_zero, smul_zero, sub_zero]

theorem hot_cold_negative_axis : prescribedExteriorRoeTransfer 2 (moving 0 3) (moving 0 1) (-Boundary.Controls.axis) = ![1/2,-2,0,0,2] := by
  have hu : averageVelocity (encode (moving 0 3)) (encode (moving 0 1)) = 0 := by
    rw [Boundary.Controls.moving_averageVelocity]
    ext j
    fin_cases j <;> rfl
  have hh : averageEnthalpy 2 (encode (moving 0 3)) (encode (moving 0 1)) = 4 := by
    rw [Boundary.Controls.moving_enthalpy]
    norm_num
  have hc : soundSpeed 2 (encode (moving 0 3)) (encode (moving 0 1)) = 2 := by
    change Real.sqrt (soundSquare 2 (encode (moving 0 3)) (encode (moving 0 1))) = 2
    rw [(averages_swap 2 (encode (moving 0 1)) (encode (moving 0 3))).2.2]
    exact Boundary.Controls.moving_sound 0
  have hd : Spectral.dissipation 2 (encode (moving 0 3)) (encode (moving 0 1)) (unitNormal (-Boundary.Controls.axis))
      (encode (moving 0 1)-encode (moving 0 3)) = ![-1,0,0,0,-4] := by
    rw [unitNormal_neg, Boundary.Controls.axis_unit, Spectral.roe_absolute_reverse]
    unfold Spectral.dissipation
    rw [hu, hh, hc, Boundary.Controls.absolute_axis]
    ext j
    fin_cases j <;> norm_num [encode, Boundary.Controls.moving]
  simp only [prescribedExteriorRoeTransfer, numericalFlux, encode_decode]
  rw [roeFluxCoordinates, ite_eq_right (neg_ne_zero.mpr Boundary.Controls.axis_ne), hd]
  ext j
  fin_cases j <;> norm_num [coordinateFlux, encode, physicalFlux, decode, Boundary.Controls.moving,
    Conservative.pressure, dot_three, squareSum_three, area, Boundary.Controls.axis]

def coldFace (F : Finset (Fin 4)) : Conservative 3 :=
  if F = primalFace standard Boundary.Controls.openPatch then moving 0 1 else moving 0 3

theorem cold_face_admissible (F : Finset (Fin 4)) : (coldFace F).Admissible 2 := by
  unfold coldFace
  split_ifs <;> apply Boundary.Controls.moving_admissible <;> norm_num

theorem hot_cold_residual : meshResidual standard 2 Boundary.Controls.mixedKinds coldFace (fun _ => moving 0 3) 0 = ![1/12,1/6,0,0,1/3] := by
  have hOutside (b : standard.Boundary) (hf : primalFace standard b ≠ primalFace standard Boundary.Controls.openPatch) :
      patchTransfer standard 2 Boundary.Controls.mixedKinds coldFace (fun _ => moving 0 3) b =
        Assembly.physicalTransfer 2 (moving 0 3) (standard.boundaryArea b) := by
    apply transfer_compatible
    · intro _
      simp [Boundary.Controls.moving, dot_three]
    · intro _
      simp [patchExterior, coldFace, hf]
  have h := Boundary.AssemblyControls.single_face_correction standard MedianDual.Controls.standard_conforming 2 Boundary.Controls.mixedKinds
    coldFace (moving 0 3) Boundary.Controls.openPatch hOutside
  change meshResidual standard 2 Boundary.Controls.mixedKinds coldFace (fun _ => moving 0 3) 0 = _ at h
  rw [h, patchTransfer_prescribed standard 2 Boundary.Controls.mixedKinds _ _ _ Boundary.Controls.mixed_corner.2.2]
  have hv : patchExterior standard coldFace Boundary.Controls.openPatch = moving 0 1 := by simp [patchExterior, coldFace]
  rw [hv, Boundary.AssemblyControls.standard_open_area, prescribed_scale 2 (1/6) _ _ _ (by norm_num), hot_cold_negative_axis]
  ext j
  fin_cases j <;> norm_num [Assembly.physicalTransfer, physicalFlux, Boundary.Controls.moving, Conservative.pressure,
    encode, dot_three, squareSum_three, Boundary.Controls.axis]

theorem negative_density_update :
    encode (meshStep standard 2 Boundary.Controls.mixedKinds coldFace (fun _ => 1) (fun _ => moving 0 3) 0) = ![-1,-4,0,0,-5] := by
  rw [mesh_step_used _ _ _ _ _ _ 0 (standard_used 0), encode_decode,
    MedianDual.Controls.standard_volume, hot_cold_residual]
  ext j
  fin_cases j <;> norm_num [encode, Boundary.Controls.moving]

theorem negative_update_not_admissible :
    ¬ (meshStep standard 2 Boundary.Controls.mixedKinds coldFace (fun _ => 1) (fun _ => moving 0 3) 0).Admissible 2 := by
  intro h
  have hρ := h.1
  change 0 < encode (meshStep standard 2 Boundary.Controls.mixedKinds coldFace (fun _ => 1) (fun _ => moving 0 3) 0) 0 at hρ
  rw [negative_density_update] at hρ
  norm_num at hρ


def unusedMesh : MedianDual.MeshData 5 1 where
  position := ![![0,0,0],![1,0,0],![0,1,0],![0,0,1],![9,9,9]]
  vertex _ := ⟨Fin.castSucc, Fin.castSucc_injective 4⟩
  positive t := by
    fin_cases t
    exact MedianDual.Controls.standard_positive

theorem unused_four : ¬unusedMesh.Used 4 := by
  rintro ⟨t,i,h⟩
  have hv := congrArg Fin.val h
  change i.val = 4 at hv
  omega

theorem unused_all (γ : ℝ) (k : Finset (Fin 5) → Kind) (V : Finset (Fin 5) → Conservative 3)
    (τ : Fin 5 → ℝ) (U : Fin 5 → Conservative 3) :
    unusedMesh.dualVolume 4 = 0 ∧ meshResidual unusedMesh γ k V U 4 = 0 ∧ meshStep unusedMesh γ k V τ U 4 = U 4 :=
  ⟨unusedMesh.dualVolume_unused 4 unused_four, mesh_residual_unused _ _ _ _ _ _ unused_four,
    mesh_step_unused _ _ _ _ _ _ _ unused_four⟩

theorem standard_mixed_common (q : ℝ) (τ : Fin 4 → ℝ) (hτ : ∀ i, 0 ≤ τ i) (i : Fin 4) :
    meshStep standard 2 Boundary.Controls.mixedKinds (fun _ => moving q 1) τ (fun _ => moving q 1) i = moving q 1 := by
  apply mesh_common_state standard MedianDual.Controls.standard_conforming 2 (by norm_num)
    _ _ τ (fun a _ => hτ a) _ (Boundary.Controls.moving_admissible q 1 (by norm_num))
  · exact Boundary.AssemblyControls.standard_wall_tangent q
  · intro b _
    rfl

theorem standard_wall_rest (τ : Fin 4 → ℝ) (hτ : ∀ i, 0 ≤ τ i) (i : Fin 4) :
    meshStep standard 2 (fun _ => .slipWall) (fun _ => moving 0 1) τ (fun _ => moving 0 1) i = moving 0 1 := by
  apply mesh_common_state standard MedianDual.Controls.standard_conforming 2 (by norm_num)
    _ _ τ (fun a _ => hτ a) _ (Boundary.Controls.moving_admissible 0 1 (by norm_num))
  · intro b _
    simp [Boundary.Controls.moving, dot_three]
  · intro b h
    cases h


theorem oblique_rest (τ : Fin 4 → ℝ) (hτ : ∀ i, 0 ≤ τ i) (i : Fin 4) :
    meshStep MedianDual.Controls.oblique 2 (fun _ => .inviscidSymmetryTraction) (fun _ => moving 0 1) τ (fun _ => moving 0 1) i = moving 0 1 := by
  apply mesh_common_state MedianDual.Controls.oblique MedianDual.Controls.oblique_conforming 2 (by norm_num)
    _ _ τ (fun a _ => hτ a) _ (Boundary.Controls.moving_admissible 0 1 (by norm_num))
  · intro b _
    simp [Boundary.Controls.moving, dot_three]
  · intro b h
    cases h

theorem two_cell_common (q : ℝ) (τ : Fin 5 → ℝ) (hτ : ∀ i, 0 ≤ τ i) (i : Fin 5) :
    meshStep Boundary.AssemblyControls.twoCells 2 Boundary.AssemblyControls.twoKinds (fun _ => moving q 1) τ (fun _ => moving q 1) i = moving q 1 := by
  apply mesh_common_state _ MedianDual.Controls.two_cells_conforming 2 (by norm_num)
    _ _ τ (fun a _ => hτ a) _ (Boundary.Controls.moving_admissible q 1 (by norm_num))
  · exact Boundary.AssemblyControls.two_wall_tangent q
  · intro b _
    rfl

abbrev twoCells := Boundary.AssemblyControls.twoCells
def twoSteps (i : Fin 5) : ℝ := ((i.val : ℝ) + 1) / 96
def twoData (F : Finset (Fin 5)) : Conservative 3 :=
  if F = primalFace twoCells Boundary.AssemblyControls.twoOpen then moving 0 3 else moving 0 1

def edge01 : twoCells.Edge := ⟨(0,1), by exact ⟨by decide,0,by decide,by decide⟩⟩
def edge03 : twoCells.Edge := ⟨(0,3), by exact ⟨by decide,0,by decide,by decide⟩⟩

theorem transported_nonconstant (i : Fin 5) :
    heldStep (fun x => twoCells.Used ((Equiv.swap 0 3).symm x))
      (fun x => twoCells.dualVolume ((Equiv.swap 0 3).symm x)) (fun x => twoSteps ((Equiv.swap 0 3).symm x))
      (stationaryResidual (twoCells.interfaces.reindex (Equiv.swap 0 3) (Equiv.swap edge01 edge03)
        (Equiv.swap Boundary.AssemblyControls.twoWall Boundary.AssemblyControls.twoOpen)) 2
        (fun x => patchKind twoCells Boundary.AssemblyControls.twoKinds ((Equiv.swap Boundary.AssemblyControls.twoWall Boundary.AssemblyControls.twoOpen).symm x))
        (fun x => patchExterior twoCells twoData ((Equiv.swap Boundary.AssemblyControls.twoWall Boundary.AssemblyControls.twoOpen).symm x))
        (fun x => Boundary.AssemblyControls.varyingStates ((Equiv.swap 0 3).symm x))
        (fun x => twoCells.edgeArea ((Equiv.swap edge01 edge03).symm x))
        (fun x => twoCells.boundaryArea ((Equiv.swap Boundary.AssemblyControls.twoWall Boundary.AssemblyControls.twoOpen).symm x)))
      (fun x => Boundary.AssemblyControls.varyingStates ((Equiv.swap 0 3).symm x)) ((Equiv.swap 0 3) i) =
      meshStep twoCells 2 Boundary.AssemblyControls.twoKinds twoData twoSteps Boundary.AssemblyControls.varyingStates i :=
  mesh_step_reindex twoCells _ _ _ 2 _ _ _ _ i

theorem transported_fields_nonconstant : twoCells.dualVolume 0 ≠ twoCells.dualVolume 3 ∧ twoSteps 0 ≠ twoSteps 3 ∧
    Boundary.AssemblyControls.varyingStates 0 ≠ Boundary.AssemblyControls.varyingStates 3 ∧
    twoData (primalFace twoCells Boundary.AssemblyControls.twoOpen) ≠ twoData (primalFace twoCells Boundary.AssemblyControls.twoWall) := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [MedianDual.Controls.two_cells_volume, MedianDual.Controls.two_cells_volume]
    rw [ite_eq_left (by decide : (0 : Fin 5).val < 3), ite_eq_right (by decide : ¬(3 : Fin 5).val < 3)]
    norm_num
  · simp only [twoSteps, show (0 : Fin 5).val = 0 from rfl, show (3 : Fin 5).val = 3 from rfl]
    norm_num
  · intro h
    have hh := congrArg Conservative.energy h
    norm_num [Boundary.AssemblyControls.varyingStates, Boundary.Controls.moving, Fin.reduceFinMk] at hh
  · have hf : primalFace twoCells Boundary.AssemblyControls.twoWall ≠ primalFace twoCells Boundary.AssemblyControls.twoOpen := by decide
    simp only [twoData, ite_eq_right hf]
    intro h
    have hh := congrArg Conservative.energy h
    norm_num [Boundary.Controls.moving] at hh

end CFDLean.Time.Controls
