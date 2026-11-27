import CFDLean.Exec.FV1DRefinement
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.RealSqrt

noncomputable section
namespace CFDLean.Exec.FV1D

private def wave (ρ : ℝ) := triple ρ ρ (2+ρ/2)
private def model := euler (1 : ℝ) 2 2 abs Real.sqrt max

private theorem entry (half dx dt : ℝ) (old : Array (EulerState ℝ))
    (j : Nat) (hj : j < old.size) :
    (stepArray model half dx dt old)[j]'(by simpa using hj) =
      model.sub old[j]
        (model.scale (dt/dx) (model.sub
          (face model half old[j] old[(j+1)%old.size]'(succ_mod_lt ⟨j, hj⟩))
          (face model half old[(j+old.size-1)%old.size]'(pred_mod_lt ⟨j, hj⟩) old[j]))) := by
  exact Array.getElem_ofFn _

/-- Nine entries of the actual array output, including the wraparound face. -/
example : stepArray model (1/2) 1 (1/16) #[wave 1, wave 4, wave 9] =
    #[triple (35/16) (35/16) (99/32), triple (121/32) (121/32) (249/64),
      triple (257/32) (257/32) (385/64)] := by
  apply Array.ext (by simp)
  intro j hj _
  have h : j < 3 := by simpa using hj
  rw [entry _ _ _ _ j (by simpa using hj)]
  funext k
  interval_cases j <;> fin_cases k <;> norm_num [face, model, euler, pressure, wave]

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
  rw [entry _ _ _ _ 0 (by simp)]
  funext k
  fin_cases k <;> norm_num [face, model, euler, pressure]

example : stepArray model (1/2) 1 0 #[wave 1, wave 4, wave 9] = #[wave 1, wave 4, wave 9] := by
  apply Array.ext (by simp)
  intro j hj _
  rw [entry _ _ _ _ j (by simpa using hj)]
  funext k
  simp [model, euler]

end CFDLean.Exec.FV1D
