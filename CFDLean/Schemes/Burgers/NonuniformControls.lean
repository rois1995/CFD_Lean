import CFDLean.Schemes.Burgers.Nonuniform

/-! Exact controls FVN-X and FVN-BC for Burgers on a non-uniform periodic 1D mesh.

Four cells with widths `(1, 3, 1, 1)` (`fvnMesh`) and the state `fvnState = (0, 1, 6/5, 0)`, whose width-weighted sum
is `21/5`.

- FVN-X (`meshRatio_needed`): the mesh ratio holds for `θ = 5/4` and fails for `θ = 2`. At cell 1 the rescaled
  differences are `back = 3/2` and `fwd = 3/10`. Minmod and van Albada keep the left state at face 1 in `[0, 6/5]`;
  van Leer, MC, superbee and the unlimited slope leave it.
- FVN-BC: one first-order and one minmod MUSCL step with `dt = 1/10`, their width-weighted sums, and two wrong-width
  mutations: the unrescaled B3 slope (`1/5` instead of `3/10`) and the update fed with the unrescaled B3 face fluxes
  (`81/4000` instead of `289/16000` in cell 0). Cell 3 only sees the seam face. The FVN-MB CFL premise
  `8 · (1/10) · max (|0|, |6/5|) = 24/25 ≤ w i` holds at every cell. -/
noncomputable section
namespace CFDLean.Burgers.Nonuniform

open CFDLean.Periodic
open CFDLean.Scalar.FiniteVolume (minmod centralSlope limitedSlope mcFactor superbeeFactor vanLeerFactor
  vanAlbadaFactor boundedStates)

/-! ### Control data -/

/-- The FVN-X and FVN-BC mesh: four periodic cells with widths `(1, 3, 1, 1)`. -/
def fvnMesh : Mesh1D (ZMod 4) where
  grid := zmodGrid 4
  width := ![1, 3, 1, 1]
  width_pos := by
    intro i
    fin_cases i <;> norm_num

/-- The FVN-X and FVN-BC state `(0, 1, 6/5, 0)`. -/
def fvnState : ZMod 4 → ℝ := ![0, 1, 6 / 5, 0]

/-! ### Index and value lemmas -/

private theorem cases4 (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i
  decide

private theorem grid_fvnMesh : fvnMesh.grid = zmodGrid 4 := rfl

private theorem next_0 : (zmodGrid 4).next 0 = 1 := rfl
private theorem next_1 : (zmodGrid 4).next 1 = 2 := rfl
private theorem next_2 : (zmodGrid 4).next 2 = 3 := rfl
private theorem next_3 : (zmodGrid 4).next 3 = 0 := rfl
private theorem prev_0 : (zmodGrid 4).prev 0 = 3 := rfl
private theorem prev_1 : (zmodGrid 4).prev 1 = 0 := rfl
private theorem prev_2 : (zmodGrid 4).prev 2 = 1 := rfl
private theorem prev_3 : (zmodGrid 4).prev 3 = 2 := rfl

private theorem w_0 : fvnMesh.width 0 = 1 := rfl
private theorem w_1 : fvnMesh.width 1 = 3 := rfl
private theorem w_2 : fvnMesh.width 2 = 1 := rfl
private theorem w_3 : fvnMesh.width 3 = 1 := rfl

private theorem u_0 : fvnState 0 = 0 := rfl
private theorem u_1 : fvnState 1 = 1 := rfl
private theorem u_2 : fvnState 2 = 6 / 5 := rfl
private theorem u_3 : fvnState 3 = 0 := rfl

/-! ### FVN-X: left state at face 1 for each limiter -/

/-- FVN-X: the rescaled backward difference of cell 1 is `(3 / 2) · (1 - 0) = 3/2`. -/
theorem backDiff_fvnMesh_one : FV1D.Nonuniform.backDiff fvnMesh fvnState 1 = 3 / 2 := by
  simp only [FV1D.Nonuniform.backDiff, Mesh1D.spacing, grid_fvnMesh, prev_1, next_0, w_0, w_1, u_0, u_1,
    smul_eq_mul]
  norm_num

/-- FVN-X: the rescaled forward difference of cell 1 is `(3 / 2) · (6/5 - 1) = 3/10`. -/
theorem fwdDiff_fvnMesh_one : FV1D.Nonuniform.fwdDiff fvnMesh fvnState 1 = 3 / 10 := by
  simp only [FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_fvnMesh, next_1, w_1, w_2, u_1, u_2, smul_eq_mul]
  norm_num

/-- At cell 1 the rescaled differences are `back = 3/2` and `fwd = 3/10`. -/
private theorem leftState_fvnMesh_one (φ : ℝ → ℝ → ℝ) :
    FV1D.Nonuniform.leftState fvnMesh φ fvnState 1 = 1 + φ (3 / 2) (3 / 10) / 2 := by
  simp only [FV1D.Nonuniform.leftState, FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff,
    FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_fvnMesh, next_0, next_1, prev_1, w_0, w_1, w_2, u_0, u_1, u_2,
    smul_eq_mul]
  norm_num
  ring

/-- FVN-X, minmod: `1 + 3/20 = 23/20`, inside `[0, 6/5]`. -/
theorem leftState_fvnMesh_minmod : FV1D.Nonuniform.leftState fvnMesh minmod fvnState 1 = 23 / 20 := by
  rw [leftState_fvnMesh_one]; norm_num [minmod]

/-- FVN-X, van Albada: `61/52`, inside `[0, 6/5]`. -/
theorem leftState_fvnMesh_vanAlbada :
    FV1D.Nonuniform.leftState fvnMesh (limitedSlope vanAlbadaFactor) fvnState 1 = 61 / 52 := by
  rw [leftState_fvnMesh_one]; norm_num [limitedSlope, vanAlbadaFactor, centralSlope]

/-- FVN-X, van Leer: `5/4`, above `6/5`. -/
theorem leftState_fvnMesh_vanLeer :
    FV1D.Nonuniform.leftState fvnMesh (limitedSlope vanLeerFactor) fvnState 1 = 5 / 4 := by
  rw [leftState_fvnMesh_one]; norm_num [limitedSlope, vanLeerFactor, centralSlope]

/-- FVN-X, MC: `13/10`, above `6/5`. -/
theorem leftState_fvnMesh_mc : FV1D.Nonuniform.leftState fvnMesh (limitedSlope mcFactor) fvnState 1 = 13 / 10 := by
  rw [leftState_fvnMesh_one]; norm_num [limitedSlope, mcFactor, centralSlope]

/-- FVN-X, superbee: `13/10`, above `6/5`. -/
theorem leftState_fvnMesh_superbee :
    FV1D.Nonuniform.leftState fvnMesh (limitedSlope superbeeFactor) fvnState 1 = 13 / 10 := by
  rw [leftState_fvnMesh_one]; norm_num [limitedSlope, superbeeFactor, centralSlope]

/-- FVN-X, unlimited central slope: `29/20`, above `6/5`. -/
theorem leftState_fvnMesh_central : FV1D.Nonuniform.leftState fvnMesh centralSlope fvnState 1 = 29 / 20 := by
  rw [leftState_fvnMesh_one]; norm_num [centralSlope]

/-- FVN-X: the state lies in `[0, 6/5]`. -/
theorem fvnState_mem_bounded : fvnState ∈ boundedStates 0 (6 / 5) := by
  intro j
  rcases cases4 j with rfl | rfl | rfl | rfl <;> simp only [u_0, u_1, u_2, u_3] <;> norm_num

/-- FVN-X: mesh ratio `5/4` holds; the binding face is face 0 or 1, `15/4 ≤ 4`. -/
theorem fvnMesh_meshRatio : fvnMesh.MeshRatio (5 / 4) := by
  intro i
  rcases cases4 i with rfl | rfl | rfl | rfl <;>
    simp only [grid_fvnMesh, next_0, next_1, next_2, next_3, w_0, w_1, w_2, w_3] <;> norm_num

/-- FVN-X: mesh ratio `2` fails at face 0, `6 > 4`. -/
theorem fvnMesh_not_meshRatio_two : ¬ fvnMesh.MeshRatio 2 := by
  intro h
  have h0 := h 0
  rw [grid_fvnMesh, next_0, w_0, w_1] at h0
  norm_num at h0

/-- FVN-X (mesh ratio needed). The state `fvnState` lies in `[0, 6/5]` and the mesh `fvnMesh` has mesh ratio `5/4`
but not `2`. At cell 1 the rescaled differences are `back = 3/2` and `fwd = 3/10`. The left state at face 1 is `23/20`
(minmod) and `61/52` (van Albada), both in `[0, 6/5]`, and `5/4` (van Leer), `13/10` (MC, superbee) and `29/20`
(unlimited), all above `6/5`. -/
theorem meshRatio_needed :
    fvnState ∈ boundedStates 0 (6 / 5) ∧ fvnMesh.MeshRatio (5 / 4) ∧ ¬ fvnMesh.MeshRatio 2 ∧
      FV1D.Nonuniform.backDiff fvnMesh fvnState 1 = 3 / 2 ∧
      FV1D.Nonuniform.fwdDiff fvnMesh fvnState 1 = 3 / 10 ∧
      FV1D.Nonuniform.leftState fvnMesh minmod fvnState 1 = 23 / 20 ∧
      FV1D.Nonuniform.leftState fvnMesh (limitedSlope vanAlbadaFactor) fvnState 1 = 61 / 52 ∧
      FV1D.Nonuniform.leftState fvnMesh (limitedSlope vanLeerFactor) fvnState 1 = 5 / 4 ∧
      FV1D.Nonuniform.leftState fvnMesh (limitedSlope mcFactor) fvnState 1 = 13 / 10 ∧
      FV1D.Nonuniform.leftState fvnMesh (limitedSlope superbeeFactor) fvnState 1 = 13 / 10 ∧
      FV1D.Nonuniform.leftState fvnMesh centralSlope fvnState 1 = 29 / 20 :=
  ⟨fvnState_mem_bounded, fvnMesh_meshRatio, fvnMesh_not_meshRatio_two, backDiff_fvnMesh_one, fwdDiff_fvnMesh_one,
    leftState_fvnMesh_minmod, leftState_fvnMesh_vanAlbada, leftState_fvnMesh_vanLeer, leftState_fvnMesh_mc,
    leftState_fvnMesh_superbee, leftState_fvnMesh_central⟩

/-! ### FVN-BC: first-order step

The face fluxes `face (u i) (u (next i))` are `-1/4`, `49/100`, `27/25` and `0`. -/

private theorem sum_fvnMesh (f : ZMod 4 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

/-- FVN-BC: the initial width-weighted sum is `1 · 0 + 3 · 1 + 1 · 6/5 + 1 · 0 = 21/5`. -/
theorem fvnState_sum : ∑ i, fvnMesh.width i * fvnState i = 21 / 5 := by
  rw [sum_fvnMesh, w_0, w_1, w_2, w_3, u_0, u_1, u_2, u_3]
  norm_num

/-- FVN-BC: the FVN-MB CFL premise with `dt = 1/10` and the bounds `[0, 6/5]` holds at every cell:
`8 · (1/10) · max (|0|, |6/5|) = 24/25 ≤ 1 ≤ w i`. -/
theorem fvnMesh_cfl : ∀ i, 8 * (1 / 10 : ℝ) * max |(0 : ℝ)| |6 / 5| ≤ fvnMesh.width i := by
  have h : 8 * (1 / 10 : ℝ) * max |(0 : ℝ)| |6 / 5| = 24 / 25 := by
    rw [abs_zero, abs_of_pos (by norm_num : (0 : ℝ) < 6 / 5), max_eq_right (by norm_num)]
    norm_num
  intro i
  rw [h]
  rcases cases4 i with rfl | rfl | rfl | rfl <;> simp only [w_0, w_1, w_2, w_3] <;> norm_num

private theorem foFace_0 : face (fvnState 0) (fvnState 1) = -1 / 4 := by
  rw [u_0, u_1]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem foFace_1 : face (fvnState 1) (fvnState 2) = 49 / 100 := by
  rw [u_1, u_2]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem foFace_2 : face (fvnState 2) (fvnState 3) = 27 / 25 := by
  rw [u_2, u_3]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem foFace_3 : face (fvnState 3) (fvnState 0) = 0 := by
  rw [u_3, u_0]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem firstOrderStep_fvnMesh_0 : firstOrderStep fvnMesh (1 / 10) fvnState 0 = 1 / 40 := by
  simp only [firstOrderStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_fvnMesh, next_0, prev_0,
    next_3, foFace_0, foFace_3]
  rw [u_0, w_0]; norm_num

private theorem firstOrderStep_fvnMesh_1 : firstOrderStep fvnMesh (1 / 10) fvnState 1 = 1463 / 1500 := by
  simp only [firstOrderStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_fvnMesh, next_1, prev_1,
    next_0, foFace_1, foFace_0]
  rw [u_1, w_1]; norm_num

private theorem firstOrderStep_fvnMesh_2 : firstOrderStep fvnMesh (1 / 10) fvnState 2 = 1141 / 1000 := by
  simp only [firstOrderStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_fvnMesh, next_2, prev_2,
    next_1, foFace_2, foFace_1]
  rw [u_2, w_2]; norm_num

private theorem firstOrderStep_fvnMesh_3 : firstOrderStep fvnMesh (1 / 10) fvnState 3 = 27 / 250 := by
  simp only [firstOrderStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_fvnMesh, next_3, prev_3,
    next_2, foFace_3, foFace_2]
  rw [u_3, w_3]; norm_num

/-- FVN-BC: the first-order step with `dt = 1/10`. -/
theorem firstOrderStep_fvnMesh :
    firstOrderStep fvnMesh (1 / 10) fvnState = ![1 / 40, 1463 / 1500, 1141 / 1000, 27 / 250] := by
  funext i
  rcases cases4 i with rfl | rfl | rfl | rfl
  exacts [firstOrderStep_fvnMesh_0, firstOrderStep_fvnMesh_1, firstOrderStep_fvnMesh_2, firstOrderStep_fvnMesh_3]

/-- FVN-BC: the first-order step keeps the width-weighted sum `21/5`. -/
theorem firstOrderStep_fvnMesh_sum :
    ∑ i, fvnMesh.width i * firstOrderStep fvnMesh (1 / 10) fvnState i = 21 / 5 := by
  rw [sum_fvnMesh, w_0, w_1, w_2, w_3, firstOrderStep_fvnMesh_0, firstOrderStep_fvnMesh_1, firstOrderStep_fvnMesh_2,
    firstOrderStep_fvnMesh_3]
  norm_num

/-! ### FVN-BC: minmod MUSCL step

The rescaled minmod slopes are `0`, `3/10`, `0`, `0`; the face states are `(0, 17/20)`, `(23/20, 6/5)`, `(6/5, 0)`
and `(0, 0)`; the face fluxes are `-289/1600`, `1057/1600`, `27/25` and `0`. -/

private theorem slope_fvnMesh_0 : FV1D.Nonuniform.slope fvnMesh minmod fvnState 0 = 0 := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_fvnMesh,
    next_0, prev_0, next_3, w_0, w_1, w_3, u_0, u_1, u_3, smul_eq_mul]
  norm_num [minmod]

/-- FVN-BC: the rescaled minmod slope of cell 1 is `3/10`. -/
theorem slope_fvnMesh_minmod : FV1D.Nonuniform.slope fvnMesh minmod fvnState 1 = 3 / 10 := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_fvnMesh,
    next_1, prev_1, next_0, w_0, w_1, w_2, u_0, u_1, u_2, smul_eq_mul]
  norm_num [minmod]

private theorem slope_fvnMesh_2 : FV1D.Nonuniform.slope fvnMesh minmod fvnState 2 = 0 := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_fvnMesh,
    next_2, prev_2, next_1, w_1, w_2, w_3, u_1, u_2, u_3, smul_eq_mul]
  norm_num [minmod]

private theorem slope_fvnMesh_3 : FV1D.Nonuniform.slope fvnMesh minmod fvnState 3 = 0 := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_fvnMesh,
    next_3, prev_3, next_2, w_2, w_3, w_0, u_2, u_3, u_0, smul_eq_mul]
  norm_num [minmod]

private theorem left_0 : FV1D.Nonuniform.leftState fvnMesh minmod fvnState 0 = 0 := by
  simp only [FV1D.Nonuniform.leftState, slope_fvnMesh_0, u_0, smul_eq_mul]; norm_num

private theorem left_2 : FV1D.Nonuniform.leftState fvnMesh minmod fvnState 2 = 6 / 5 := by
  simp only [FV1D.Nonuniform.leftState, slope_fvnMesh_2, u_2, smul_eq_mul]; norm_num

private theorem left_3 : FV1D.Nonuniform.leftState fvnMesh minmod fvnState 3 = 0 := by
  simp only [FV1D.Nonuniform.leftState, slope_fvnMesh_3, u_3, smul_eq_mul]; norm_num

private theorem right_0 : FV1D.Nonuniform.rightState fvnMesh minmod fvnState 0 = 17 / 20 := by
  simp only [FV1D.Nonuniform.rightState, grid_fvnMesh, next_0, slope_fvnMesh_minmod, u_1, smul_eq_mul]; norm_num

private theorem right_1 : FV1D.Nonuniform.rightState fvnMesh minmod fvnState 1 = 6 / 5 := by
  simp only [FV1D.Nonuniform.rightState, grid_fvnMesh, next_1, slope_fvnMesh_2, u_2, smul_eq_mul]; norm_num

private theorem right_2 : FV1D.Nonuniform.rightState fvnMesh minmod fvnState 2 = 0 := by
  simp only [FV1D.Nonuniform.rightState, grid_fvnMesh, next_2, slope_fvnMesh_3, u_3, smul_eq_mul]; norm_num

private theorem right_3 : FV1D.Nonuniform.rightState fvnMesh minmod fvnState 3 = 0 := by
  simp only [FV1D.Nonuniform.rightState, grid_fvnMesh, next_3, slope_fvnMesh_0, u_0, smul_eq_mul]; norm_num

private theorem mFace_0 :
    face (FV1D.Nonuniform.leftState fvnMesh minmod fvnState 0)
      (FV1D.Nonuniform.rightState fvnMesh minmod fvnState 0) = -289 / 1600 := by
  rw [left_0, right_0]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem mFace_1 :
    face (FV1D.Nonuniform.leftState fvnMesh minmod fvnState 1)
      (FV1D.Nonuniform.rightState fvnMesh minmod fvnState 1) = 1057 / 1600 := by
  rw [leftState_fvnMesh_minmod, right_1]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem mFace_2 :
    face (FV1D.Nonuniform.leftState fvnMesh minmod fvnState 2)
      (FV1D.Nonuniform.rightState fvnMesh minmod fvnState 2) = 27 / 25 := by
  rw [left_2, right_2]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem mFace_3 :
    face (FV1D.Nonuniform.leftState fvnMesh minmod fvnState 3)
      (FV1D.Nonuniform.rightState fvnMesh minmod fvnState 3) = 0 := by
  rw [left_3, right_3]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem musclStep_fvnMesh_0 : musclStep fvnMesh (1 / 10) minmod fvnState 0 = 289 / 16000 := by
  simp only [musclStep, FV1D.Nonuniform.musclStep, FV1D.Nonuniform.update, grid_fvnMesh, prev_0, mFace_0, mFace_3]
  rw [u_0, w_0]; norm_num

private theorem musclStep_fvnMesh_1 : musclStep fvnMesh (1 / 10) minmod fvnState 1 = 23327 / 24000 := by
  simp only [musclStep, FV1D.Nonuniform.musclStep, FV1D.Nonuniform.update, grid_fvnMesh, prev_1, mFace_1, mFace_0]
  rw [u_1, w_1]; norm_num

private theorem musclStep_fvnMesh_2 : musclStep fvnMesh (1 / 10) minmod fvnState 2 = 18529 / 16000 := by
  simp only [musclStep, FV1D.Nonuniform.musclStep, FV1D.Nonuniform.update, grid_fvnMesh, prev_2, mFace_2, mFace_1]
  rw [u_2, w_2]; norm_num

private theorem musclStep_fvnMesh_3 : musclStep fvnMesh (1 / 10) minmod fvnState 3 = 27 / 250 := by
  simp only [musclStep, FV1D.Nonuniform.musclStep, FV1D.Nonuniform.update, grid_fvnMesh, prev_3, mFace_3, mFace_2]
  rw [u_3, w_3]; norm_num

/-- FVN-BC: the minmod MUSCL step with `dt = 1/10`. -/
theorem musclStep_fvnMesh_minmod :
    musclStep fvnMesh (1 / 10) minmod fvnState = ![289 / 16000, 23327 / 24000, 18529 / 16000, 27 / 250] := by
  funext i
  rcases cases4 i with rfl | rfl | rfl | rfl
  exacts [musclStep_fvnMesh_0, musclStep_fvnMesh_1, musclStep_fvnMesh_2, musclStep_fvnMesh_3]

/-- FVN-BC: the minmod MUSCL step keeps the width-weighted sum `21/5`. -/
theorem musclStep_fvnMesh_minmod_sum :
    ∑ i, fvnMesh.width i * musclStep fvnMesh (1 / 10) minmod fvnState i = 21 / 5 := by
  rw [sum_fvnMesh, w_0, w_1, w_2, w_3, musclStep_fvnMesh_0, musclStep_fvnMesh_1, musclStep_fvnMesh_2,
    musclStep_fvnMesh_3]
  norm_num

/-! ### FVN-BC: wrong-width mutations

The B3 reconstruction without rescaling, on the same widths: slope `1/5` in cell 1, face fluxes `-81/400` (face 0)
and `0` (face 3). -/

/-- FVN-BC mutation: the unrescaled B3 minmod slope of cell 1 is `1/5`. -/
theorem b3_slope_fvnMesh_minmod : Scalar.FiniteVolume.slope (zmodGrid 4) minmod fvnState 1 = 1 / 5 := by
  simp only [Scalar.FiniteVolume.slope, next_1, prev_1, u_0, u_1, u_2]
  norm_num [minmod]

private theorem b3Flux_0 :
    Scalar.FiniteVolume.musclFlux (zmodGrid 4) Rusanov.numericalFlux minmod fvnState 0 = -81 / 400 := by
  simp only [Scalar.FiniteVolume.musclFlux, Scalar.FiniteVolume.leftState, Scalar.FiniteVolume.rightState,
    Scalar.FiniteVolume.slope, next_0, next_1, prev_0, prev_1, u_0, u_1, u_2, u_3]
  norm_num [minmod, Rusanov.numericalFlux, Rusanov.eval, physicalFlux, Rusanov.waveSpeed]

private theorem b3Flux_3 :
    Scalar.FiniteVolume.musclFlux (zmodGrid 4) Rusanov.numericalFlux minmod fvnState 3 = 0 := by
  simp only [Scalar.FiniteVolume.musclFlux, Scalar.FiniteVolume.leftState, Scalar.FiniteVolume.rightState,
    Scalar.FiniteVolume.slope, next_3, prev_3, next_0, prev_0, u_0, u_1, u_2, u_3]
  norm_num [minmod, Rusanov.numericalFlux, Rusanov.eval, physicalFlux, Rusanov.waveSpeed]

/-- FVN-BC mutation: the update on the same widths fed with the unrescaled B3 minmod face fluxes gives `81/4000` in
cell 0, not `289/16000`. -/
theorem b3_update_fvnMesh_minmod :
    FV1D.Nonuniform.update fvnMesh (1 / 10)
      (Scalar.FiniteVolume.musclFlux (zmodGrid 4) Rusanov.numericalFlux minmod fvnState) fvnState 0 = 81 / 4000 := by
  simp only [FV1D.Nonuniform.update, grid_fvnMesh, prev_0, b3Flux_0, b3Flux_3]
  rw [u_0, w_0]; norm_num

end CFDLean.Burgers.Nonuniform
