import CFDLean.Exec.FV1DRefinement
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.RealSqrt

noncomputable section
namespace CFDLean.Exec.FV1D

private def wave (ρ : ℝ) := triple ρ ρ (2+ρ/2)
private def model := euler (1 : ℝ) 2 2 abs Real.sqrt max

/-- Nine entries of the actual array output, including the wraparound face. -/
example : stepArray model (1/2) 1 (1/16) #[wave 1, wave 4, wave 9] =
    #[triple (35/16) (35/16) (99/32), triple (121/32) (121/32) (249/64),
      triple (257/32) (257/32) (385/64)] := by
  apply Array.ext (by simp)
  intro j hj _
  have h : j < 3 := by simpa using hj
  funext k
  simp only [stepArray, Array.getElem_ofFn, Fin.getElem_fin, face, model, euler, pressure]
  interval_cases j <;> fin_cases k <;> norm_num [wave]

example : stepArray burgers (1/2) 1 (1/8) #[(1 : ℝ), -2, 4] =
    eulerStepArray 1 (1/8) #[1, -2, 4] := by
  let old : Array ℝ := #[1, -2, 4]
  exact (burgers_refines (n := 3) 1 (1/8) (by norm_num) (by norm_num)
    (fun j => old[j.val]'(j.val_lt)) old (samples_entries old rfl).symm).2

example : stepArray model (1/2) 1 1 #[] = #[] := Array.eq_empty_of_size_eq_zero (by simp)

example : stepArray model (1/2) 1 1 #[triple 1 2 3] = #[triple 1 2 3] := by
  apply Array.ext (by simp)
  intro j hj _
  have h : j < 1 := by simpa using hj
  have hj' : j = 0 := by omega
  subst j
  funext k
  simp only [stepArray, Array.getElem_ofFn, Fin.getElem_fin, face, model, euler, pressure]
  fin_cases k <;> norm_num

example : stepArray model (1/2) 1 0 #[wave 1, wave 4, wave 9] = #[wave 1, wave 4, wave 9] := by
  apply Array.ext (by simp)
  intro j hj _
  funext k
  simp only [stepArray, Array.getElem_ofFn, Fin.getElem_fin, model, euler, zero_div, zero_mul, sub_zero]

end CFDLean.Exec.FV1D
