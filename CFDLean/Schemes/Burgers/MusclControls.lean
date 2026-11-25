import CFDLean.Schemes.Burgers.RusanovMuscl

/-! Exact small controls for Burgers B3. -/
noncomputable section
namespace CFDLean.Burgers.MusclControls

open CFDLean.Burgers CFDLean.Scalar.FiniteVolume
open CFDLean.Burgers.Schemes.RusanovForwardEuler

example : minmod 1 2 = 1 := by norm_num [minmod]

example : minmod 3 2 = 2 := by norm_num [minmod]

example : minmod (-3) (-2) = -2 := by norm_num [minmod]

-- Opposite signs (a local extremum): the slope is zero.
example : minmod (-1) 2 = 0 := by norm_num [minmod]

example : minmod 1 0 = 0 := by norm_num [minmod]

-- The zero limiter gives the first-order scheme of B0.
example (dx dt : ℝ) (u : ZMod 5 → ℝ) : Rusanov.musclEulerStep grid dx dt (fun _ _ => 0) u = step dx dt u := by
  funext i
  simp [Rusanov.musclEulerStep, step, semidiscrete, Time.ForwardEuler.step, musclRhs_zero]

example (dx dt c : ℝ) : Rusanov.musclSsprk3Step (grid (N := 4)) dx dt minmod (fun _ => c) = fun _ => c :=
  Rusanov.musclSsprk3Step_constant _ dx dt minmod c

end CFDLean.Burgers.MusclControls
