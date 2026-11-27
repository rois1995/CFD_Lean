import CFDLean.Schemes.Burgers.Nonuniform

/-! Exact controls FVN-X and FVN-BC for Burgers on a non-uniform periodic 1D mesh.

Four cells with widths `(1, 3, 1, 1)` and the state `u4 = (0, 1, 6/5, 0)`.

- FVN-X (`meshRatio_needed`): the mesh ratio holds for `θ = 5/4` and fails for `θ = 2`. At cell 1 the rescaled
  differences are `back = 3/2` and `fwd = 3/10`. Minmod and van Albada keep the left state at face 1 in `[0, 6/5]`;
  van Leer, MC, superbee and the unlimited slope leave it.
- FVN-BC: one first-order and one minmod MUSCL step with `dt = 1/10`, their width-weighted sums, and two wrong-width
  mutations: the unrescaled B3 slope (`1/5` instead of `3/10`) and the update fed with the unrescaled B3 face fluxes
  (`81/4000` instead of `289/16000` in cell 0). Cell 3 only sees the seam face. -/
noncomputable section
namespace CFDLean.Burgers.Nonuniform

open CFDLean.Periodic
open CFDLean.Scalar.FiniteVolume (minmod centralSlope limitedSlope mcFactor superbeeFactor vanLeerFactor
  vanAlbadaFactor boundedStates)

/-! ### Control data -/

/-- The FVN-X and FVN-BC mesh: four periodic cells with widths `(1, 3, 1, 1)`. -/
def m4 : Mesh1D (ZMod 4) where
  grid := zmodGrid 4
  width := ![1, 3, 1, 1]
  width_pos := by
    intro i
    fin_cases i <;> norm_num

/-- The FVN-X and FVN-BC state `(0, 1, 6/5, 0)`. -/
def u4 : ZMod 4 → ℝ := ![0, 1, 6 / 5, 0]

/-! ### Index and value lemmas -/

private theorem cases4 (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i
  decide

private theorem grid_m4 : m4.grid = zmodGrid 4 := rfl

private theorem next_0 : (zmodGrid 4).next 0 = 1 := rfl
private theorem next_1 : (zmodGrid 4).next 1 = 2 := rfl
private theorem next_2 : (zmodGrid 4).next 2 = 3 := rfl
private theorem next_3 : (zmodGrid 4).next 3 = 0 := rfl
private theorem prev_0 : (zmodGrid 4).prev 0 = 3 := rfl
private theorem prev_1 : (zmodGrid 4).prev 1 = 0 := rfl
private theorem prev_2 : (zmodGrid 4).prev 2 = 1 := rfl
private theorem prev_3 : (zmodGrid 4).prev 3 = 2 := rfl

private theorem w_0 : m4.width 0 = 1 := rfl
private theorem w_1 : m4.width 1 = 3 := rfl
private theorem w_2 : m4.width 2 = 1 := rfl
private theorem w_3 : m4.width 3 = 1 := rfl

private theorem u_0 : u4 0 = 0 := rfl
private theorem u_1 : u4 1 = 1 := rfl
private theorem u_2 : u4 2 = 6 / 5 := rfl
private theorem u_3 : u4 3 = 0 := rfl

/-! ### FVN-X: left state at face 1 for each limiter -/

/-- At cell 1 the rescaled differences are `back = 3/2` and `fwd = 3/10`. -/
private theorem leftState_m4_one (φ : ℝ → ℝ → ℝ) :
    FV1D.Nonuniform.leftState m4 φ u4 1 = 1 + φ (3 / 2) (3 / 10) / 2 := by
  simp only [FV1D.Nonuniform.leftState, FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff,
    FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_m4, next_0, next_1, prev_1, w_0, w_1, w_2, u_0, u_1, u_2,
    smul_eq_mul]
  norm_num
  ring

/-- FVN-X, minmod: `1 + 3/20 = 23/20`, inside `[0, 6/5]`. -/
theorem leftState_m4_minmod : FV1D.Nonuniform.leftState m4 minmod u4 1 = 23 / 20 := by
  rw [leftState_m4_one]; norm_num [minmod]

/-- FVN-X, van Albada: `61/52`, inside `[0, 6/5]`. -/
theorem leftState_m4_vanAlbada : FV1D.Nonuniform.leftState m4 (limitedSlope vanAlbadaFactor) u4 1 = 61 / 52 := by
  rw [leftState_m4_one]; norm_num [limitedSlope, vanAlbadaFactor, centralSlope]

/-- FVN-X, van Leer: `5/4`, above `6/5`. -/
theorem leftState_m4_vanLeer : FV1D.Nonuniform.leftState m4 (limitedSlope vanLeerFactor) u4 1 = 5 / 4 := by
  rw [leftState_m4_one]; norm_num [limitedSlope, vanLeerFactor, centralSlope]

/-- FVN-X, MC: `13/10`, above `6/5`. -/
theorem leftState_m4_mc : FV1D.Nonuniform.leftState m4 (limitedSlope mcFactor) u4 1 = 13 / 10 := by
  rw [leftState_m4_one]; norm_num [limitedSlope, mcFactor, centralSlope]

/-- FVN-X, superbee: `13/10`, above `6/5`. -/
theorem leftState_m4_superbee : FV1D.Nonuniform.leftState m4 (limitedSlope superbeeFactor) u4 1 = 13 / 10 := by
  rw [leftState_m4_one]; norm_num [limitedSlope, superbeeFactor, centralSlope]

/-- FVN-X, unlimited central slope: `29/20`, above `6/5`. -/
theorem leftState_m4_central : FV1D.Nonuniform.leftState m4 centralSlope u4 1 = 29 / 20 := by
  rw [leftState_m4_one]; norm_num [centralSlope]

/-- FVN-X: the state lies in `[0, 6/5]`. -/
theorem u4_mem_bounded : u4 ∈ boundedStates 0 (6 / 5) := by
  intro j
  rcases cases4 j with rfl | rfl | rfl | rfl <;> simp only [u_0, u_1, u_2, u_3] <;> norm_num

/-- FVN-X: mesh ratio `5/4` holds; the binding face is face 0 or 1, `15/4 ≤ 4`. -/
theorem m4_meshRatio : m4.MeshRatio (5 / 4) := by
  intro i
  rcases cases4 i with rfl | rfl | rfl | rfl <;>
    simp only [grid_m4, next_0, next_1, next_2, next_3, w_0, w_1, w_2, w_3] <;> norm_num

/-- FVN-X: mesh ratio `2` fails at face 0, `6 > 4`. -/
theorem m4_not_meshRatio_two : ¬ m4.MeshRatio 2 := by
  intro h
  have h0 := h 0
  rw [grid_m4, next_0, w_0, w_1] at h0
  norm_num at h0

/-- FVN-X (mesh ratio needed). The state `u4` lies in `[0, 6/5]` and the mesh `m4` has mesh ratio `5/4` but not `2`.
The left state at face 1 is `23/20` (minmod) and `61/52` (van Albada), both in `[0, 6/5]`, and `5/4` (van Leer),
`13/10` (MC, superbee) and `29/20` (unlimited), all above `6/5`. -/
theorem meshRatio_needed :
    u4 ∈ boundedStates 0 (6 / 5) ∧ m4.MeshRatio (5 / 4) ∧ ¬ m4.MeshRatio 2 ∧
      FV1D.Nonuniform.leftState m4 minmod u4 1 = 23 / 20 ∧
      FV1D.Nonuniform.leftState m4 (limitedSlope vanAlbadaFactor) u4 1 = 61 / 52 ∧
      FV1D.Nonuniform.leftState m4 (limitedSlope vanLeerFactor) u4 1 = 5 / 4 ∧
      FV1D.Nonuniform.leftState m4 (limitedSlope mcFactor) u4 1 = 13 / 10 ∧
      FV1D.Nonuniform.leftState m4 (limitedSlope superbeeFactor) u4 1 = 13 / 10 ∧
      FV1D.Nonuniform.leftState m4 centralSlope u4 1 = 29 / 20 :=
  ⟨u4_mem_bounded, m4_meshRatio, m4_not_meshRatio_two, leftState_m4_minmod, leftState_m4_vanAlbada,
    leftState_m4_vanLeer, leftState_m4_mc, leftState_m4_superbee, leftState_m4_central⟩

/-! ### FVN-BC: first-order step

The face fluxes `face (u i) (u (next i))` are `-1/4`, `49/100`, `27/25` and `0`. -/

private theorem sum_m4 (f : ZMod 4 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

private theorem foFace_0 : face (u4 0) (u4 1) = -1 / 4 := by
  rw [u_0, u_1]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem foFace_1 : face (u4 1) (u4 2) = 49 / 100 := by
  rw [u_1, u_2]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem foFace_2 : face (u4 2) (u4 3) = 27 / 25 := by
  rw [u_2, u_3]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem foFace_3 : face (u4 3) (u4 0) = 0 := by
  rw [u_3, u_0]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem firstOrderStep_m4_0 : firstOrderStep m4 (1 / 10) u4 0 = 1 / 40 := by
  simp only [firstOrderStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_m4, next_0, prev_0,
    next_3, foFace_0, foFace_3]
  rw [u_0, w_0]; norm_num

private theorem firstOrderStep_m4_1 : firstOrderStep m4 (1 / 10) u4 1 = 1463 / 1500 := by
  simp only [firstOrderStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_m4, next_1, prev_1,
    next_0, foFace_1, foFace_0]
  rw [u_1, w_1]; norm_num

private theorem firstOrderStep_m4_2 : firstOrderStep m4 (1 / 10) u4 2 = 1141 / 1000 := by
  simp only [firstOrderStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_m4, next_2, prev_2,
    next_1, foFace_2, foFace_1]
  rw [u_2, w_2]; norm_num

private theorem firstOrderStep_m4_3 : firstOrderStep m4 (1 / 10) u4 3 = 27 / 250 := by
  simp only [firstOrderStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_m4, next_3, prev_3,
    next_2, foFace_3, foFace_2]
  rw [u_3, w_3]; norm_num

/-- FVN-BC: the first-order step with `dt = 1/10`. -/
theorem firstOrderStep_m4 : firstOrderStep m4 (1 / 10) u4 = ![1 / 40, 1463 / 1500, 1141 / 1000, 27 / 250] := by
  funext i
  rcases cases4 i with rfl | rfl | rfl | rfl
  exacts [firstOrderStep_m4_0, firstOrderStep_m4_1, firstOrderStep_m4_2, firstOrderStep_m4_3]

/-- FVN-BC: the first-order step keeps the width-weighted sum `21/5`. -/
theorem firstOrderStep_m4_sum : ∑ i, m4.width i * firstOrderStep m4 (1 / 10) u4 i = 21 / 5 := by
  rw [sum_m4, w_0, w_1, w_2, w_3, firstOrderStep_m4_0, firstOrderStep_m4_1, firstOrderStep_m4_2,
    firstOrderStep_m4_3]
  norm_num

/-! ### FVN-BC: minmod MUSCL step

The rescaled minmod slopes are `0`, `3/10`, `0`, `0`; the face states are `(0, 17/20)`, `(23/20, 6/5)`, `(6/5, 0)`
and `(0, 0)`; the face fluxes are `-289/1600`, `1057/1600`, `27/25` and `0`. -/

private theorem slope_m4_0 : FV1D.Nonuniform.slope m4 minmod u4 0 = 0 := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_m4,
    next_0, prev_0, next_3, w_0, w_1, w_3, u_0, u_1, u_3, smul_eq_mul]
  norm_num [minmod]

/-- FVN-BC: the rescaled minmod slope of cell 1 is `3/10`. -/
theorem slope_m4_minmod : FV1D.Nonuniform.slope m4 minmod u4 1 = 3 / 10 := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_m4,
    next_1, prev_1, next_0, w_0, w_1, w_2, u_0, u_1, u_2, smul_eq_mul]
  norm_num [minmod]

private theorem slope_m4_2 : FV1D.Nonuniform.slope m4 minmod u4 2 = 0 := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_m4,
    next_2, prev_2, next_1, w_1, w_2, w_3, u_1, u_2, u_3, smul_eq_mul]
  norm_num [minmod]

private theorem slope_m4_3 : FV1D.Nonuniform.slope m4 minmod u4 3 = 0 := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_m4,
    next_3, prev_3, next_2, w_2, w_3, w_0, u_2, u_3, u_0, smul_eq_mul]
  norm_num [minmod]

private theorem left_0 : FV1D.Nonuniform.leftState m4 minmod u4 0 = 0 := by
  simp only [FV1D.Nonuniform.leftState, slope_m4_0, u_0, smul_eq_mul]; norm_num

private theorem left_2 : FV1D.Nonuniform.leftState m4 minmod u4 2 = 6 / 5 := by
  simp only [FV1D.Nonuniform.leftState, slope_m4_2, u_2, smul_eq_mul]; norm_num

private theorem left_3 : FV1D.Nonuniform.leftState m4 minmod u4 3 = 0 := by
  simp only [FV1D.Nonuniform.leftState, slope_m4_3, u_3, smul_eq_mul]; norm_num

private theorem right_0 : FV1D.Nonuniform.rightState m4 minmod u4 0 = 17 / 20 := by
  simp only [FV1D.Nonuniform.rightState, grid_m4, next_0, slope_m4_minmod, u_1, smul_eq_mul]; norm_num

private theorem right_1 : FV1D.Nonuniform.rightState m4 minmod u4 1 = 6 / 5 := by
  simp only [FV1D.Nonuniform.rightState, grid_m4, next_1, slope_m4_2, u_2, smul_eq_mul]; norm_num

private theorem right_2 : FV1D.Nonuniform.rightState m4 minmod u4 2 = 0 := by
  simp only [FV1D.Nonuniform.rightState, grid_m4, next_2, slope_m4_3, u_3, smul_eq_mul]; norm_num

private theorem right_3 : FV1D.Nonuniform.rightState m4 minmod u4 3 = 0 := by
  simp only [FV1D.Nonuniform.rightState, grid_m4, next_3, slope_m4_0, u_0, smul_eq_mul]; norm_num

private theorem mFace_0 :
    face (FV1D.Nonuniform.leftState m4 minmod u4 0) (FV1D.Nonuniform.rightState m4 minmod u4 0) = -289 / 1600 := by
  rw [left_0, right_0]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem mFace_1 :
    face (FV1D.Nonuniform.leftState m4 minmod u4 1) (FV1D.Nonuniform.rightState m4 minmod u4 1) = 1057 / 1600 := by
  rw [leftState_m4_minmod, right_1]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem mFace_2 :
    face (FV1D.Nonuniform.leftState m4 minmod u4 2) (FV1D.Nonuniform.rightState m4 minmod u4 2) = 27 / 25 := by
  rw [left_2, right_2]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem mFace_3 :
    face (FV1D.Nonuniform.leftState m4 minmod u4 3) (FV1D.Nonuniform.rightState m4 minmod u4 3) = 0 := by
  rw [left_3, right_3]; norm_num [face, FV1D.face, physicalFlux, Rusanov.waveSpeed]

private theorem musclStep_m4_0 : musclStep m4 (1 / 10) minmod u4 0 = 289 / 16000 := by
  simp only [musclStep, FV1D.Nonuniform.musclStep, FV1D.Nonuniform.update, grid_m4, prev_0, mFace_0, mFace_3]
  rw [u_0, w_0]; norm_num

private theorem musclStep_m4_1 : musclStep m4 (1 / 10) minmod u4 1 = 23327 / 24000 := by
  simp only [musclStep, FV1D.Nonuniform.musclStep, FV1D.Nonuniform.update, grid_m4, prev_1, mFace_1, mFace_0]
  rw [u_1, w_1]; norm_num

private theorem musclStep_m4_2 : musclStep m4 (1 / 10) minmod u4 2 = 18529 / 16000 := by
  simp only [musclStep, FV1D.Nonuniform.musclStep, FV1D.Nonuniform.update, grid_m4, prev_2, mFace_2, mFace_1]
  rw [u_2, w_2]; norm_num

private theorem musclStep_m4_3 : musclStep m4 (1 / 10) minmod u4 3 = 27 / 250 := by
  simp only [musclStep, FV1D.Nonuniform.musclStep, FV1D.Nonuniform.update, grid_m4, prev_3, mFace_3, mFace_2]
  rw [u_3, w_3]; norm_num

/-- FVN-BC: the minmod MUSCL step with `dt = 1/10`. -/
theorem musclStep_m4_minmod :
    musclStep m4 (1 / 10) minmod u4 = ![289 / 16000, 23327 / 24000, 18529 / 16000, 27 / 250] := by
  funext i
  rcases cases4 i with rfl | rfl | rfl | rfl
  exacts [musclStep_m4_0, musclStep_m4_1, musclStep_m4_2, musclStep_m4_3]

/-- FVN-BC: the minmod MUSCL step keeps the width-weighted sum `21/5`. -/
theorem musclStep_m4_minmod_sum : ∑ i, m4.width i * musclStep m4 (1 / 10) minmod u4 i = 21 / 5 := by
  rw [sum_m4, w_0, w_1, w_2, w_3, musclStep_m4_0, musclStep_m4_1, musclStep_m4_2, musclStep_m4_3]
  norm_num

/-! ### FVN-BC: wrong-width mutations

The B3 reconstruction without rescaling, on the same widths: slope `1/5` in cell 1, face fluxes `-81/400` (face 0)
and `0` (face 3). -/

/-- FVN-BC mutation: the unrescaled B3 minmod slope of cell 1 is `1/5`. -/
theorem b3_slope_m4_minmod : Scalar.FiniteVolume.slope (zmodGrid 4) minmod u4 1 = 1 / 5 := by
  simp only [Scalar.FiniteVolume.slope, next_1, prev_1, u_0, u_1, u_2]
  norm_num [minmod]

private theorem b3Flux_0 :
    Scalar.FiniteVolume.musclFlux (zmodGrid 4) Rusanov.numericalFlux minmod u4 0 = -81 / 400 := by
  simp only [Scalar.FiniteVolume.musclFlux, Scalar.FiniteVolume.leftState, Scalar.FiniteVolume.rightState,
    Scalar.FiniteVolume.slope, next_0, next_1, prev_0, prev_1, u_0, u_1, u_2, u_3]
  norm_num [minmod, Rusanov.numericalFlux, Rusanov.eval, physicalFlux, Rusanov.waveSpeed]

private theorem b3Flux_3 :
    Scalar.FiniteVolume.musclFlux (zmodGrid 4) Rusanov.numericalFlux minmod u4 3 = 0 := by
  simp only [Scalar.FiniteVolume.musclFlux, Scalar.FiniteVolume.leftState, Scalar.FiniteVolume.rightState,
    Scalar.FiniteVolume.slope, next_3, prev_3, next_0, prev_0, u_0, u_1, u_2, u_3]
  norm_num [minmod, Rusanov.numericalFlux, Rusanov.eval, physicalFlux, Rusanov.waveSpeed]

/-- FVN-BC mutation: the update on the same widths fed with the unrescaled B3 minmod face fluxes gives `81/4000` in
cell 0, not `289/16000`. -/
theorem b3_update_m4_minmod :
    FV1D.Nonuniform.update m4 (1 / 10)
      (Scalar.FiniteVolume.musclFlux (zmodGrid 4) Rusanov.numericalFlux minmod u4) u4 0 = 81 / 4000 := by
  simp only [FV1D.Nonuniform.update, grid_m4, prev_0, b3Flux_0, b3Flux_3]
  rw [u_0, w_0]; norm_num

end CFDLean.Burgers.Nonuniform
