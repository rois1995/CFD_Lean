import CFDLean.Schemes.Burgers.RusanovLimiters

/-! Exact small controls for Burgers B3b. -/
noncomputable section
namespace CFDLean.Burgers.LimiterControls

open CFDLean.Burgers CFDLean.Scalar.FiniteVolume

-- Unlimited: the slope is the central difference.
example : limitedSlope noLimiter 1 3 = 2 := by norm_num [limitedSlope, noLimiter, centralSlope]

-- On a smooth monotone profile with equal differences every limiter has the factor 1.
example : minmodFactor 2 2 = 1 := by norm_num [minmodFactor]

example : mcFactor 2 2 = 1 := by norm_num [mcFactor]

example : superbeeFactor 2 2 = 1 := by norm_num [superbeeFactor]

example : vanLeerFactor 2 2 = 1 := by norm_num [vanLeerFactor]

example : vanAlbadaFactor 2 2 = 1 := by norm_num [vanAlbadaFactor]

-- Differences 1 and 3: minmod 1/2, MC 1, superbee 1, van Leer 3/4, van Albada 3/5.
example : minmodFactor 1 3 = 1 / 2 := by norm_num [minmodFactor]

example : mcFactor 1 3 = 1 := by norm_num [mcFactor]

example : superbeeFactor 1 3 = 1 := by norm_num [superbeeFactor]

example : vanLeerFactor 1 3 = 3 / 4 := by norm_num [vanLeerFactor]

example : vanAlbadaFactor 1 3 = 3 / 5 := by norm_num [vanAlbadaFactor]

-- Superbee is compressive: its factor reaches 4/3.
example : superbeeFactor 1 2 = 4 / 3 := by norm_num [superbeeFactor]

-- At a local extremum (opposite signs) every limiter switches the slope off; the unlimited slope does not.
example : vanAlbadaFactor 1 (-2) = 0 := by norm_num [vanAlbadaFactor]

example : limitedSlope noLimiter 1 (-2) = -1 / 2 := by norm_num [limitedSlope, noLimiter, centralSlope]

-- The unlimited scheme leaves the bounds of the state; the same step with a limiter does not.
example : (1 : ℝ) < Rusanov.musclEulerStep Schemes.RusanovForwardEuler.grid 1 (1 / 10) centralSlope
    Rusanov.stepData 3 := by
  rw [Rusanov.unlimited_step_leaves_bounds.2]
  norm_num

example : Rusanov.musclEulerStep Schemes.RusanovForwardEuler.grid 1 (1 / 10) (limitedSlope vanLeerFactor)
    Rusanov.stepData ∈ boundedStates 0 1 :=
  Rusanov.musclEulerStep_mem_bounded _ 1 (1 / 10) 0 1 _ 2 slopeBounded_vanLeerFactor le_rfl one_pos (by norm_num)
    (by norm_num) _ Rusanov.stepData_mem

end CFDLean.Burgers.LimiterControls
