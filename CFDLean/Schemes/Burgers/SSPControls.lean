import CFDLean.Schemes.Burgers.RusanovSSP

/-! Exact small controls for Burgers B2. -/
noncomputable section
namespace CFDLean.Burgers.SSPControls

open CFDLean.Burgers CFDLean.Time
open CFDLean.Burgers.Schemes.RusanovForwardEuler

-- With the one-step map `x ↦ x + 1` (Forward Euler for `x' = 1`, `dt = 1`) both SSP steps advance by exactly 1.
example : SSP.ssprk2 (fun x : ℝ => x + 1) 0 = 1 := by
  norm_num [SSP.ssprk2]

example : SSP.ssprk3 (fun x : ℝ => x + 1) 0 = 1 := by
  norm_num [SSP.ssprk3]

-- With the one-step map `x ↦ x + x` (Forward Euler for `x' = x`, `dt = 1`): SSPRK2 gives `1 + 1 + 1/2`,
-- SSPRK3 gives `1 + 1 + 1/2 + 1/6`, the Taylor polynomials of `e`.
example : SSP.ssprk2 (fun x : ℝ => x + x) 1 = 5 / 2 := by
  norm_num [SSP.ssprk2]

example : SSP.ssprk3 (fun x : ℝ => x + x) 1 = 8 / 3 := by
  norm_num [SSP.ssprk3]

example (dx dt c : ℝ) : Rusanov.ssprk3Step (grid (N := 4)) dx dt (fun _ => c) = fun _ => c :=
  Rusanov.ssprk3Step_constant _ dx dt c

example (dx dt : ℝ) (u : ZMod 4 → ℝ) : (step (N := 4) dx dt)^[3] u = (Rusanov.eulerStep grid dx dt)^[3] u := by
  rw [step_eq_eulerStep]

end CFDLean.Burgers.SSPControls
