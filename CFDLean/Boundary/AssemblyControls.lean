import CFDLean.Boundary.Assembly
import CFDLean.Boundary.Controls
import CFDLean.Geometry.MedianDual.TwoCells

noncomputable section
namespace CFDLean.Boundary.AssemblyControls
open Coordinates PhysicalJacobian Roe
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
attribute [local irreducible] Spectral.shift Spectral.b Spectral.dp Spectral.minus Spectral.plus Spectral.zero

abbrev standard := Controls.standard
abbrev wallPatch := Controls.wallPatch
abbrev openPatch := Controls.openPatch
abbrev mixedKinds := Controls.mixedKinds
abbrev moving := Controls.moving

theorem same_face_area {n m : ℕ} (M : MedianDual.MeshData n m) (b c : M.Boundary)
    (hf : primalFace M b = primalFace M c) : M.boundaryArea b = M.boundaryArea c := by
  have ho := M.faceCount_one_unique b.1.1 c.1.1 b.prop.1 hf.symm
  unfold MedianDual.MeshData.boundaryArea
  rw [ho]

theorem standard_wall_area : standard.boundaryArea wallPatch = ![0,0,-1/6] := by
  ext j
  fin_cases j <;> norm_num [MedianDual.MeshData.boundaryArea, MedianDual.MeshData.faceArea,
    MedianDual.MeshData.points, MedianDual.Controls.standard, MedianDual.Controls.oneCell,
    MedianDual.Controls.standardBoundary, MedianDual.Controls.standardPoints, MedianDual.faceVector,
    MedianDual.triangle, MedianDual.cross]

theorem standard_open_area : standard.boundaryArea openPatch = (1/6 : ℝ) • (-Controls.axis) := by
  ext j
  fin_cases j <;> norm_num [MedianDual.MeshData.boundaryArea, MedianDual.MeshData.faceArea,
    MedianDual.MeshData.points, MedianDual.Controls.standard, MedianDual.Controls.oneCell,
    Controls.openPatch, MedianDual.Controls.standardPoints, MedianDual.faceVector,
    MedianDual.triangle, MedianDual.cross, Controls.axis]

theorem standard_wall_tangent (q : ℝ) (b : standard.Boundary)
    (hk : patchKind standard mixedKinds b ≠ .prescribedExteriorRoe) :
    dot (moving q 1).momentum (standard.boundaryArea b) = 0 := by
  have hf : primalFace standard b = primalFace standard wallPatch := by
    by_contra hn
    exact hk (by simp [patchKind, Controls.mixedKinds, hn])
  rw [same_face_area standard b wallPatch hf, standard_wall_area]
  norm_num [Controls.moving, dot_three]

theorem standard_mixed_common (q : ℝ) (i : Fin 4) :
    meshResidual standard 2 mixedKinds (fun _ => moving q 1) (fun _ => moving q 1) i = 0 := by
  apply mesh_constant_state standard MedianDual.Controls.standard_conforming 2 (by norm_num)
    (moving q 1) (Controls.moving_admissible q 1 (by norm_num))
  · exact standard_wall_tangent q
  · intro b _
    rfl

theorem standard_all_wall_rest (V : Finset (Fin 4) → Conservative 3) (i : Fin 4) :
    meshResidual standard 2 (fun _ => .slipWall) V (fun _ => moving 0 1) i = 0 := by
  apply mesh_constant_state standard MedianDual.Controls.standard_conforming 2 (by norm_num)
    (moving 0 1) (Controls.moving_admissible 0 1 (by norm_num))
  · intro b _
    simp [Controls.moving, dot_three]
  · intro b h
    cases h

/-- Exact bookkeeping of a selected-rule mismatch supported on one actual primal face. -/
theorem single_face_correction {n m : ℕ} (M : MedianDual.MeshData n m) (hM : M.Conforming)
    (γ : ℝ) (k : Finset (Fin n) → Kind) (V : Finset (Fin n) → Conservative 3)
    (U : Conservative 3) (b₀ : M.Boundary)
    (hOutside : ∀ b : M.Boundary, primalFace M b ≠ primalFace M b₀ →
      patchTransfer M γ k V (fun _ => U) b = Assembly.physicalTransfer γ U (M.boundaryArea b)) :
    meshResidual M γ k V (fun _ => U) (M.interfaces.owner b₀) =
      patchTransfer M γ k V (fun _ => U) b₀ - Assembly.physicalTransfer γ U (M.boundaryArea b₀) := by
  classical
  rw [mesh_common_correction M hM]
  have ht (b : M.Boundary) :
      (if M.interfaces.owner b = M.interfaces.owner b₀ then
        patchTransfer M γ k V (fun _ => U) b - Assembly.physicalTransfer γ U (M.boundaryArea b) else 0) =
      if b = b₀ then patchTransfer M γ k V (fun _ => U) b₀ - Assembly.physicalTransfer γ U (M.boundaryArea b₀) else 0 := by
    by_cases hb : b = b₀
    · subst b
      simp
    · by_cases hi : M.interfaces.owner b = M.interfaces.owner b₀
      · have hf : primalFace M b ≠ primalFace M b₀ := fun h => hb (boundary_record_unique M b b₀ h hi)
        simp [hb, hi, hOutside b hf]
      · simp [hb, hi]
  simp_rw [ht]
  simp

def normalState : Conservative 3 := ⟨1, ![0,0,1], 3/2⟩
theorem normal_admissible : normalState.Admissible 2 := by
  norm_num [normalState, Conservative.Admissible, Conservative.pressure, squareSum_three]

theorem incompatible_wall_residual :
    meshResidual standard 2 mixedKinds (fun _ => normalState) (fun _ => normalState) 0 = ![1/6,0,0,1/6,5/12] := by
  have hOutside (b : standard.Boundary) (hf : primalFace standard b ≠ primalFace standard wallPatch) :
      patchTransfer standard 2 mixedKinds (fun _ => normalState) (fun _ => normalState) b =
        Assembly.physicalTransfer 2 normalState (standard.boundaryArea b) := by
    have hk : patchKind standard mixedKinds b = .prescribedExteriorRoe := by simp [patchKind, Controls.mixedKinds, hf]
    rw [patchTransfer_prescribed standard 2 mixedKinds _ _ b hk]
    exact prescribed_consistency 2 normalState _
  have hc := single_face_correction standard MedianDual.Controls.standard_conforming 2 mixedKinds
    (fun _ => normalState) normalState wallPatch hOutside
  change meshResidual standard 2 mixedKinds (fun _ => normalState) (fun _ => normalState) 0 = _ at hc
  rw [hc, patchTransfer_wall standard 2 mixedKinds _ _ wallPatch Controls.mixed_corner.2.1, standard_wall_area]
  ext j
  fin_cases j <;> norm_num [wallTransfer, pressureTransfer, Assembly.physicalTransfer, physicalFlux,
    normalState, Conservative.pressure, encode, dot_three, squareSum_three]

theorem negative_axis_flux : prescribedExteriorRoeTransfer 2 (moving 0 1) (moving 0 3) (-Controls.axis) = ![-1/2,-2,0,0,-2] := by
  have hu : averageVelocity (encode (moving 0 1)) (encode (moving 0 3)) = 0 := by
    rw [Controls.moving_averageVelocity]
    ext j
    fin_cases j <;> rfl
  have hh : averageEnthalpy 2 (encode (moving 0 1)) (encode (moving 0 3)) = 4 := by
    rw [Controls.moving_enthalpy]
    norm_num
  have hd : Spectral.dissipation 2 (encode (moving 0 1)) (encode (moving 0 3)) (unitNormal (-Controls.axis))
      (encode (moving 0 3)-encode (moving 0 1)) = ![1,0,0,0,4] := by
    rw [unitNormal_neg, Controls.axis_unit, Spectral.roe_absolute_reverse]
    unfold Spectral.dissipation
    rw [hu, hh, Controls.moving_sound, Controls.absolute_axis]
    ext j
    fin_cases j <;> norm_num [encode, Controls.moving]
  simp only [prescribedExteriorRoeTransfer, numericalFlux, encode_decode]
  rw [roeFluxCoordinates, if_neg (neg_ne_zero.mpr Controls.axis_ne), hd]
  ext j
  fin_cases j <;> norm_num [coordinateFlux, encode, physicalFlux, decode, Controls.moving,
    Conservative.pressure, dot_three, squareSum_three, area, Controls.axis]

def mismatchingData (F : Finset (Fin 4)) : Conservative 3 :=
  if F = primalFace standard openPatch then moving 0 3 else moving 0 1

theorem mismatching_data_admissible (F : Finset (Fin 4)) : (mismatchingData F).Admissible 2 := by
  unfold mismatchingData
  split_ifs <;> apply Controls.moving_admissible <;> norm_num

theorem incompatible_exterior_residual :
    meshResidual standard 2 mixedKinds mismatchingData (fun _ => moving 0 1) 0 = ![-1/12,-1/6,0,0,-1/3] := by
  have hOutside (b : standard.Boundary) (hf : primalFace standard b ≠ primalFace standard openPatch) :
      patchTransfer standard 2 mixedKinds mismatchingData (fun _ => moving 0 1) b =
        Assembly.physicalTransfer 2 (moving 0 1) (standard.boundaryArea b) := by
    apply transfer_compatible 2 (patchKind standard mixedKinds b) (moving 0 1) (patchExterior standard mismatchingData b) (standard.boundaryArea b)
    · intro _
      simp [Controls.moving, dot_three]
    · intro _
      simp [patchExterior, mismatchingData, hf]
  have hc := single_face_correction standard MedianDual.Controls.standard_conforming 2 mixedKinds
    mismatchingData (moving 0 1) openPatch hOutside
  change meshResidual standard 2 mixedKinds mismatchingData (fun _ => moving 0 1) 0 = _ at hc
  rw [hc, patchTransfer_prescribed standard 2 mixedKinds _ _ openPatch Controls.mixed_corner.2.2]
  have hv : patchExterior standard mismatchingData openPatch = moving 0 3 := by simp [patchExterior, mismatchingData]
  rw [hv, standard_open_area, prescribed_scale 2 (1/6) _ _ _ (by norm_num), negative_axis_flux]
  ext j
  fin_cases j <;> norm_num [Assembly.physicalTransfer, physicalFlux, Controls.moving, Conservative.pressure,
    encode, dot_three, squareSum_three, Controls.axis]

abbrev twoCells := MedianDual.Controls.twoCells
def twoWall : twoCells.Boundary := ⟨((0,2),0), by decide⟩
def twoSymmetry : twoCells.Boundary := ⟨((1,1),0), by decide⟩
def twoOpen : twoCells.Boundary := ⟨((0,1),0), by decide⟩
def twoKinds (F : Finset (Fin 5)) : Kind :=
  if F = primalFace twoCells twoWall then .slipWall else
  if F = primalFace twoCells twoSymmetry then .inviscidSymmetryTraction else .prescribedExteriorRoe

theorem two_wall_area : twoCells.boundaryArea twoWall = ![0,-1/6,0] := by
  ext j
  fin_cases j <;> norm_num [MedianDual.MeshData.boundaryArea, MedianDual.MeshData.faceArea,
    MedianDual.MeshData.points, twoWall, MedianDual.Controls.twoCells, MedianDual.Controls.twoVertex,
    MedianDual.Controls.upperVertex, MedianDual.Controls.lowerVertex, MedianDual.Controls.twoPosition,
    MedianDual.faceVector, MedianDual.triangle, MedianDual.cross]

theorem two_symmetry_area : twoCells.boundaryArea twoSymmetry = ![0,-1/6,0] := by
  ext j
  fin_cases j <;> norm_num [MedianDual.MeshData.boundaryArea, MedianDual.MeshData.faceArea,
    MedianDual.MeshData.points, twoSymmetry, MedianDual.Controls.twoCells, MedianDual.Controls.twoVertex,
    MedianDual.Controls.upperVertex, MedianDual.Controls.lowerVertex, MedianDual.Controls.twoPosition,
    MedianDual.faceVector, MedianDual.triangle, MedianDual.cross]

theorem two_wall_tangent (q : ℝ) (b : twoCells.Boundary) (hk : patchKind twoCells twoKinds b ≠ .prescribedExteriorRoe) :
    dot (moving q 1).momentum (twoCells.boundaryArea b) = 0 := by
  by_cases hw : primalFace twoCells b = primalFace twoCells twoWall
  · rw [same_face_area twoCells b twoWall hw, two_wall_area]
    norm_num [Controls.moving, dot_three]
  · by_cases hs : primalFace twoCells b = primalFace twoCells twoSymmetry
    · rw [same_face_area twoCells b twoSymmetry hs, two_symmetry_area]
      norm_num [Controls.moving, dot_three]
    · exact False.elim (hk (by simp [patchKind, twoKinds, hw, hs]))

theorem two_cell_common (q : ℝ) (i : Fin 5) :
    meshResidual twoCells 2 twoKinds (fun _ => moving q 1) (fun _ => moving q 1) i = 0 := by
  apply mesh_constant_state twoCells MedianDual.Controls.two_cells_conforming 2 (by norm_num)
    (moving q 1) (Controls.moving_admissible q 1 (by norm_num))
  · exact two_wall_tangent q
  · intro b _
    rfl

theorem two_cell_corner : twoCells.interfaces.owner twoWall = twoCells.interfaces.owner twoSymmetry ∧
    twoCells.interfaces.owner twoWall = twoCells.interfaces.owner twoOpen ∧
    patchKind twoCells twoKinds twoWall = .slipWall ∧
    patchKind twoCells twoKinds twoSymmetry = .inviscidSymmetryTraction ∧
    patchKind twoCells twoKinds twoOpen = .prescribedExteriorRoe := by
  refine ⟨rfl,rfl,?_,?_,?_⟩
  · simp [patchKind, twoKinds]
  · have h : primalFace twoCells twoSymmetry ≠ primalFace twoCells twoWall := by decide
    simp [patchKind, twoKinds, h]
  · have h1 : primalFace twoCells twoOpen ≠ primalFace twoCells twoWall := by decide
    have h2 : primalFace twoCells twoOpen ≠ primalFace twoCells twoSymmetry := by decide
    simp [patchKind, twoKinds, h1, h2]

theorem two_cell_all_wall_mass (U : Fin 5 → Conservative 3) (V : Finset (Fin 5) → Conservative 3) :
    (∑ i, meshResidual twoCells 2 (fun _ => .slipWall) V U i 0) = 0 := by
  rw [show (∑ i, meshResidual twoCells 2 (fun _ => .slipWall) V U i 0) = _ from
    stationary_mass_balance twoCells.interfaces 2 (patchKind twoCells (fun _ => .slipWall)) (patchExterior twoCells V) U twoCells.edgeArea twoCells.boundaryArea]
  simp [patchKind]

theorem two_cell_all_wall_energy (U : Fin 5 → Conservative 3) (V : Finset (Fin 5) → Conservative 3) :
    (∑ i, meshResidual twoCells 2 (fun _ => .slipWall) V U i 4) = 0 := by
  rw [show (∑ i, meshResidual twoCells 2 (fun _ => .slipWall) V U i 4) = _ from
    stationary_energy_balance twoCells.interfaces 2 (patchKind twoCells (fun _ => .slipWall)) (patchExterior twoCells V) U twoCells.edgeArea twoCells.boundaryArea]
  simp [patchKind]

def edge01 : standard.Edge := ⟨(0,1), by exact ⟨by decide, 0, by decide, by decide⟩⟩
def edge02 : standard.Edge := ⟨(0,2), by exact ⟨by decide, 0, by decide, by decide⟩⟩

theorem transported_nonzero :
    stationaryResidual (standard.interfaces.reindex (Equiv.swap 0 1) (Equiv.swap edge01 edge02) (Equiv.swap wallPatch openPatch)) 2
      (fun b => patchKind standard mixedKinds ((Equiv.swap wallPatch openPatch).symm b))
      (fun b => patchExterior standard mismatchingData ((Equiv.swap wallPatch openPatch).symm b))
      (fun _ => moving 0 1)
      (fun e => standard.edgeArea ((Equiv.swap edge01 edge02).symm e))
      (fun b => standard.boundaryArea ((Equiv.swap wallPatch openPatch).symm b)) 1 = ![-1/12,-1/6,0,0,-1/3] := by
  have h := mesh_residual_reindex standard (Equiv.swap 0 1) (Equiv.swap edge01 edge02) (Equiv.swap wallPatch openPatch)
    2 mixedKinds mismatchingData (fun _ => moving 0 1) 0
  simpa only [Equiv.swap_apply_left] using h.trans incompatible_exterior_residual

/-- An abstract balance control: no geometric closure is claimed for this interface. -/
def onePatchInterface : Assembly.Interfaces (Fin 2) (Fin 1) (Fin 1) where
  tail _ := 0
  head _ := 1
  distinct _ := by decide
  owner _ := 0

theorem pressure_force_retained :
    (∑ i, stationaryResidual onePatchInterface 2 (fun _ => .slipWall) (fun _ => moving 0 3)
      (fun _ => moving 0 1) (fun _ => Controls.axis) (fun _ => Controls.axis) i) = ![0,1,0,0,0] := by
  rw [stationary_global_balance]
  ext j
  fin_cases j <;> norm_num [Fin.sum_univ_one, constructedTransfer, transfer, wallTransfer,
    pressureTransfer, Controls.moving_pressure, Controls.axis]

theorem oblique_all_symmetry_rest (V : Finset (Fin 4) → Conservative 3) (i : Fin 4) :
    meshResidual MedianDual.Controls.oblique 2 (fun _ => .inviscidSymmetryTraction) V (fun _ => moving 0 1) i = 0 := by
  apply mesh_constant_state MedianDual.Controls.oblique MedianDual.Controls.oblique_conforming 2 (by norm_num)
    (moving 0 1) (Controls.moving_admissible 0 1 (by norm_num))
  · intro b _
    simp [Controls.moving, dot_three]
  · intro b h
    cases h

def varyingStates (i : Fin 5) : Conservative 3 := moving 0 ((i.val : ℝ)+1)
theorem varying_admissible (i : Fin 5) : (varyingStates i).Admissible 2 :=
  Controls.moving_admissible 0 _ (by positivity)

end CFDLean.Boundary.AssemblyControls
