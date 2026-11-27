import CFDLean.Schemes.Euler.FV1DPositivity
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.FinCases

noncomputable section
namespace CFDLean.Euler1D.Controls

attribute [local simp] Matrix.cons_val_two

private def state (ρ : ℝ) : Conservative 1 := ⟨ρ, fun _ => ρ, 2 + ρ / 2⟩
private def initial (i : ZMod 3) : Conservative 1 := state (![1, 4, 9] i)
private def massFlux (i : ZMod 3) : ℝ := ![-2, 3/2, 17] i

private theorem initial_next (i : ZMod 3) :
    initial ((Periodic.zmodGrid 3).next i) = state (![4, 9, 1] i) := by fin_cases i <;> rfl

private theorem massFlux_prev (i : ZMod 3) :
    massFlux ((Periodic.zmodGrid 3).prev i) = ![17, -2, 3/2] i := by fin_cases i <;> rfl

private theorem fluxes (i : ZMod 3) :
    FV1D.face (flux 2) (speed 2) (encode (initial i))
        (encode (initial ((Periodic.zmodGrid 3).next i))) =
      ![massFlux i, massFlux i + 2, massFlux i / 2 + 4] := by
  rw [initial_next]
  funext k
  fin_cases i <;> fin_cases k <;>
    norm_num [FV1D.face, speed, endpointSpeed, flux, initial, state, massFlux, encode, decode,
      physicalFlux, dot, Conservative.pressure, squareSum,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The ordered face mass transfers include the face across the periodic seam. -/
theorem mass_fluxes (i : ZMod 3) :
    (face 2 (initial i) (initial ((Periodic.zmodGrid 3).next i))).density = ![-2, 3/2, 17] i := by
  exact congrFun (fluxes i) 0

/-- All nine updated components of the assembled step. -/
theorem updated_cells (i : ZMod 3) :
    step 2 1 (1/16) initial i =
      ⟨![35/16, 121/32, 257/32] i, fun _ => ![35/16, 121/32, 257/32] i,
        ![99/32, 249/64, 385/64] i⟩ := by
  simp only [step, FV1D.step, fluxes, massFlux_prev]
  fin_cases i <;> norm_num [initial, state, massFlux, encode, decode,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- At the local CFL endpoint the central old-state weight of cell zero vanishes. -/
theorem cfl_endpoint_cells (i : ZMod 3) :
    step 2 1 (1/3) initial i =
      state (![22/3, 17/6, 23/6] i) := by
  simp only [step, FV1D.step, fluxes, massFlux_prev]
  fin_cases i <;> norm_num [initial, state, massFlux, encode, decode,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem cfl_endpoint_speeds (i : ZMod 3) :
    rightSpeed 2 initial i = ![3, 2, 3] i := by
  unfold rightSpeed
  rw [initial_next]
  fin_cases i <;> norm_num [speed, endpointSpeed, initial, state, encode, decode,
    Conservative.pressure, squareSum]

example (U : ZMod 3 → Conservative 1) (i : ZMod 3) : step 2 1 0 U i = U i := by
  simp [step, FV1D.step]

example (U : ZMod 1 → Conservative 1) (dt : ℝ) (i : ZMod 1) : step 2 1 dt U i = U i := by
  have he : (Periodic.zmodGrid 1).prev i = i := Subsingleton.elim _ _
  simp [step, FV1D.step, he]

end CFDLean.Euler1D.Controls
