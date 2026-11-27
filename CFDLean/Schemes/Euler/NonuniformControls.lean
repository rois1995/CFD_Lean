import CFDLean.Discrete.Periodic.Muscl
import CFDLean.Schemes.Euler.Nonuniform
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.FinCases

/-! Exact control FVN-E: the FV1D Euler control data on a non-uniform periodic 1D mesh.

Three cells with widths `(1, 2, 1)`, `γ = 2`, `dt = 1/16`, densities `(1, 4, 9)`, velocity one and pressure two, so
the states are `(ρ, ρ, 2 + ρ/2)`. The face fluxes are those of the uniform FV1D control (`CFDLean.Euler1D.Controls`).
Cells 0 and 2 match the uniform update; cell 1 has width 2 and gets half of its uniform update. The seam face from
cell 2 to cell 0 uses the widths of both cells. The full Euler MUSCL step is not a control, because the face sound
speeds are irrational; the MUSCL face states with componentwise minmod are. -/
noncomputable section
namespace CFDLean.Euler1D.NonuniformControls

open Periodic

attribute [local simp] Matrix.cons_val_two

/-- The FVN-E mesh: three periodic cells with widths `(1, 2, 1)`. -/
def m3 : Mesh1D (ZMod 3) where
  grid := zmodGrid 3
  width := ![1, 2, 1]
  width_pos := by
    intro i
    fin_cases i <;> norm_num

/-- Density `ρ`, velocity one and pressure two at `γ = 2`. -/
def state (ρ : ℝ) : Conservative 1 := ⟨ρ, fun _ => ρ, 2 + ρ / 2⟩

/-- The FVN-E initial states, densities `(1, 4, 9)`. -/
def initial (i : ZMod 3) : Conservative 1 := state (![1, 4, 9] i)

/-! ### Index and value lemmas -/

private theorem cases3 (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i
  decide

private theorem sum_m3 (f : ZMod 3 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

private theorem grid_m3 : m3.grid = zmodGrid 3 := rfl

private theorem next_0 : (zmodGrid 3).next 0 = 1 := rfl
private theorem next_1 : (zmodGrid 3).next 1 = 2 := rfl
private theorem next_2 : (zmodGrid 3).next 2 = 0 := rfl
private theorem prev_0 : (zmodGrid 3).prev 0 = 2 := rfl
private theorem prev_1 : (zmodGrid 3).prev 1 = 0 := rfl
private theorem prev_2 : (zmodGrid 3).prev 2 = 1 := rfl

private theorem w_0 : m3.width 0 = 1 := rfl
private theorem w_1 : m3.width 1 = 2 := rfl
private theorem w_2 : m3.width 2 = 1 := rfl

private theorem initial_0 : initial 0 = state 1 := rfl
private theorem initial_1 : initial 1 = state 4 := rfl
private theorem initial_2 : initial 2 = state 9 := rfl

private theorem enc_0 : encode (initial 0) = ![1, 1, 5 / 2] := by
  rw [initial_0]; funext k; fin_cases k <;> norm_num [encode, state]

private theorem enc_1 : encode (initial 1) = ![4, 4, 4] := by
  rw [initial_1]; funext k; fin_cases k <;> norm_num [encode, state]

private theorem enc_2 : encode (initial 2) = ![9, 9, 13 / 2] := by
  rw [initial_2]; funext k; fin_cases k <;> norm_num [encode, state]

/-! ### First-order step

The face fluxes are those of the uniform FV1D control: mass fluxes `-2`, `3/2`, `17`. -/

private theorem face_0 : FV1D.face (flux 2) (speed 2) ![1, 1, 5 / 2] ![4, 4, 4] = ![-2, 0, 3] := by
  funext k
  fin_cases k <;>
    norm_num [FV1D.face, speed, endpointSpeed, flux, encode, decode, physicalFlux, dot, Conservative.pressure,
      squareSum, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem face_1 : FV1D.face (flux 2) (speed 2) ![4, 4, 4] ![9, 9, 13 / 2] = ![3 / 2, 7 / 2, 19 / 4] := by
  funext k
  fin_cases k <;>
    norm_num [FV1D.face, speed, endpointSpeed, flux, encode, decode, physicalFlux, dot, Conservative.pressure,
      squareSum, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem face_2 : FV1D.face (flux 2) (speed 2) ![9, 9, 13 / 2] ![1, 1, 5 / 2] = ![17, 19, 25 / 2] := by
  funext k
  fin_cases k <;>
    norm_num [FV1D.face, speed, endpointSpeed, flux, encode, decode, physicalFlux, dot, Conservative.pressure,
      squareSum, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem step_0 : nonuniformStep 2 m3 (1 / 16) initial 0 = ⟨35 / 16, fun _ => 35 / 16, 99 / 32⟩ := by
  simp only [nonuniformStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_m3, next_0, prev_0,
    next_2, enc_0, enc_1, enc_2, face_0, face_2, w_0]
  norm_num [decode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

private theorem step_1 : nonuniformStep 2 m3 (1 / 16) initial 1 = ⟨249 / 64, fun _ => 249 / 64, 505 / 128⟩ := by
  simp only [nonuniformStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_m3, next_1, prev_1,
    next_0, enc_0, enc_1, enc_2, face_1, face_0, w_1]
  norm_num [decode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

private theorem step_2 : nonuniformStep 2 m3 (1 / 16) initial 2 = ⟨257 / 32, fun _ => 257 / 32, 385 / 64⟩ := by
  simp only [nonuniformStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, grid_m3, next_2, prev_2,
    next_1, enc_0, enc_1, enc_2, face_2, face_1, w_2]
  norm_num [decode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- FVN-E: the first-order step. Momenta equal densities. -/
theorem nonuniformStep_cells (i : ZMod 3) :
    nonuniformStep 2 m3 (1 / 16) initial i =
      ⟨![35 / 16, 249 / 64, 257 / 32] i, fun _ => ![35 / 16, 249 / 64, 257 / 32] i,
        ![99 / 32, 505 / 128, 385 / 64] i⟩ := by
  rcases cases3 i with rfl | rfl | rfl
  exacts [step_0, step_1, step_2]

/-- FVN-E: the width-weighted density total `18` before and after the step. -/
theorem density_total :
    ∑ i, m3.width i * (initial i).density = 18 ∧
      ∑ i, m3.width i * (nonuniformStep 2 m3 (1 / 16) initial i).density = 18 := by
  rw [sum_m3, sum_m3, w_0, w_1, w_2, initial_0, initial_1, initial_2, step_0, step_1, step_2]
  norm_num [state]

/-- FVN-E: the width-weighted momentum total `18` before and after the step. -/
theorem momentum_total :
    ∑ i, m3.width i * (initial i).momentum 0 = 18 ∧
      ∑ i, m3.width i * (nonuniformStep 2 m3 (1 / 16) initial i).momentum 0 = 18 := by
  rw [sum_m3, sum_m3, w_0, w_1, w_2, initial_0, initial_1, initial_2, step_0, step_1, step_2]
  norm_num [state]

/-- FVN-E: the width-weighted energy total `17` before and after the step. -/
theorem energy_total :
    ∑ i, m3.width i * (initial i).energy = 17 ∧
      ∑ i, m3.width i * (nonuniformStep 2 m3 (1 / 16) initial i).energy = 17 := by
  rw [sum_m3, sum_m3, w_0, w_1, w_2, initial_0, initial_1, initial_2, step_0, step_1, step_2]
  norm_num [state]

/-! ### MUSCL face states with componentwise minmod -/

private theorem slope_0 :
    FV1D.Nonuniform.slope m3 (FV1D.Nonuniform.componentwise Scalar.FiniteVolume.minmod)
      (fun j => encode (initial j)) 0 = ![0, 0, 0] := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_m3,
    next_0, prev_0, next_2, w_0, w_1, w_2, enc_0, enc_1, enc_2]
  funext k
  fin_cases k <;> norm_num [FV1D.Nonuniform.componentwise, Scalar.FiniteVolume.minmod, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]

private theorem slope_1 :
    FV1D.Nonuniform.slope m3 (FV1D.Nonuniform.componentwise Scalar.FiniteVolume.minmod)
      (fun j => encode (initial j)) 1 = ![4, 4, 2] := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_m3,
    next_1, prev_1, next_0, w_0, w_1, w_2, enc_0, enc_1, enc_2]
  funext k
  fin_cases k <;> norm_num [FV1D.Nonuniform.componentwise, Scalar.FiniteVolume.minmod, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]

private theorem slope_2 :
    FV1D.Nonuniform.slope m3 (FV1D.Nonuniform.componentwise Scalar.FiniteVolume.minmod)
      (fun j => encode (initial j)) 2 = ![0, 0, 0] := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, grid_m3,
    next_2, prev_2, next_1, w_0, w_1, w_2, enc_0, enc_1, enc_2]
  funext k
  fin_cases k <;> norm_num [FV1D.Nonuniform.componentwise, Scalar.FiniteVolume.minmod, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]

/-- FVN-E: without the rescaling, cell 1 would get the componentwise minmod of the raw differences `(3, 3, 3/2)` and
`(5, 5, 5/2)`, that is `(3, 3, 3/2)`, not the rescaled `(4, 4, 2)`. -/
theorem unrescaledSlope_one :
    FV1D.Nonuniform.componentwise Scalar.FiniteVolume.minmod (encode (initial 1) - encode (initial 0))
      (encode (initial 2) - encode (initial 1)) = ![3, 3, 3 / 2] := by
  rw [enc_0, enc_1, enc_2]
  funext k
  fin_cases k <;> norm_num [FV1D.Nonuniform.componentwise, Scalar.FiniteVolume.minmod, Pi.sub_apply]

/-- FVN-E: the rescaled componentwise minmod slopes `0`, `(4, 4, 2)`, `0`. -/
theorem slope_cells (i : ZMod 3) :
    FV1D.Nonuniform.slope m3 (FV1D.Nonuniform.componentwise Scalar.FiniteVolume.minmod)
        (fun j => encode (initial j)) i = ![![0, 0, 0], ![4, 4, 2], ![0, 0, 0]] i := by
  rcases cases3 i with rfl | rfl | rfl
  exacts [slope_0, slope_1, slope_2]

private theorem left_0 : musclLeft m3 Scalar.FiniteVolume.minmod initial 0 = ⟨1, fun _ => 1, 5 / 2⟩ := by
  simp only [musclLeft, FV1D.Nonuniform.leftState, slope_0, enc_0]
  norm_num [decode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

private theorem left_1 : musclLeft m3 Scalar.FiniteVolume.minmod initial 1 = ⟨6, fun _ => 6, 5⟩ := by
  simp only [musclLeft, FV1D.Nonuniform.leftState, slope_1, enc_1]
  norm_num [decode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

private theorem left_2 : musclLeft m3 Scalar.FiniteVolume.minmod initial 2 = ⟨9, fun _ => 9, 13 / 2⟩ := by
  simp only [musclLeft, FV1D.Nonuniform.leftState, slope_2, enc_2]
  norm_num [decode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

private theorem right_0 : musclRight m3 Scalar.FiniteVolume.minmod initial 0 = ⟨2, fun _ => 2, 3⟩ := by
  simp only [musclRight, FV1D.Nonuniform.rightState, grid_m3, next_0, slope_1, enc_1]
  norm_num [decode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

private theorem right_1 : musclRight m3 Scalar.FiniteVolume.minmod initial 1 = ⟨9, fun _ => 9, 13 / 2⟩ := by
  simp only [musclRight, FV1D.Nonuniform.rightState, grid_m3, next_1, slope_2, enc_2]
  norm_num [decode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

private theorem right_2 : musclRight m3 Scalar.FiniteVolume.minmod initial 2 = ⟨1, fun _ => 1, 5 / 2⟩ := by
  simp only [musclRight, FV1D.Nonuniform.rightState, grid_m3, next_2, slope_0, enc_0]
  norm_num [decode, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- FVN-E: left MUSCL states with componentwise minmod, `(1, 1, 5/2)`, `(6, 6, 5)`, `(9, 9, 13/2)`. -/
theorem musclLeft_cells (i : ZMod 3) :
    musclLeft m3 Scalar.FiniteVolume.minmod initial i =
      ⟨![1, 6, 9] i, fun _ => ![1, 6, 9] i, ![5 / 2, 5, 13 / 2] i⟩ := by
  rcases cases3 i with rfl | rfl | rfl
  exacts [left_0, left_1, left_2]

/-- FVN-E: right MUSCL states with componentwise minmod, `(2, 2, 3)`, `(9, 9, 13/2)`, `(1, 1, 5/2)`. -/
theorem musclRight_cells (i : ZMod 3) :
    musclRight m3 Scalar.FiniteVolume.minmod initial i =
      ⟨![2, 9, 1] i, fun _ => ![2, 9, 1] i, ![3, 13 / 2, 5 / 2] i⟩ := by
  rcases cases3 i with rfl | rfl | rfl
  exacts [right_0, right_1, right_2]

end CFDLean.Euler1D.NonuniformControls
