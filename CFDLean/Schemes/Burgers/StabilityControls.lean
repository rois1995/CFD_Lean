import CFDLean.Schemes.Burgers.RusanovStability

/-! Exact small controls for Burgers B1. The last control shows that the CFL hypothesis of the total-variation theorem
is necessary: on two cells with the state `(1, 0)`, `dx = 1` and `dt = 2` the total variation grows from 2 to 6. -/
noncomputable section
namespace CFDLean.Burgers.StabilityControls

open CFDLean.Burgers CFDLean.Scalar CFDLean.Scalar.FiniteVolume CFDLean.Periodic
open CFDLean.Burgers.Schemes.RusanovForwardEuler

example : Rusanov.eval 1 0 ≤ Rusanov.eval 2 0 := Rusanov.monotone.1 1 2 0 (by norm_num)

example : Rusanov.eval 0 2 ≤ Rusanov.eval 0 1 := Rusanov.monotone.2 0 1 2 (by norm_num)

example (c : ℝ) : totalVariation (grid (N := 4)) (fun _ => c) = 0 := by
  simp [totalVariation]

/-- The two-cell state `(1, 0)`. -/
def jump : ZMod 2 → ℝ := fun i => if i = 0 then 1 else 0

theorem zmod2_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

theorem zmod2_univ : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

/-- One step from `(1, 0)` with `dx = 1` gives `(1 - dt, dt)`. -/
theorem jump_step (dt : ℝ) : step (N := 2) 1 dt jump = fun i => if i = 0 then 1 - dt else dt := by
  funext i
  rcases zmod2_cases i with rfl | rfl <;>
    simp [step, semidiscrete, Time.ForwardEuler.step, FiniteVolume.rhs, FiniteVolume.interfaceFlux, grid, zmodGrid,
      Grid.prev, Rusanov.numericalFlux, Rusanov.eval, Rusanov.waveSpeed, physicalFlux, jump, zmod2_one_add_one] <;>
    ring

example : totalVariation (grid (N := 2)) jump = 2 := by
  simp [totalVariation, grid, zmodGrid, jump, zmod2_univ, zmod2_one_add_one]
  norm_num

/-- With `dt · a = dx` (CFL 1) the step swaps the two cells and the total variation stays 2. -/
example : totalVariation (grid (N := 2)) (step (N := 2) 1 1 jump) = 2 := by
  rw [jump_step]
  simp [totalVariation, grid, zmodGrid, zmod2_univ, zmod2_one_add_one]
  norm_num

/-- The CFL hypothesis is necessary: with `dt · a = 2 dx` the total variation grows from 2 to 6. -/
example : totalVariation (grid (N := 2)) (step (N := 2) 1 2 jump) = 6 := by
  rw [jump_step]
  simp [totalVariation, grid, zmodGrid, zmod2_univ, zmod2_one_add_one]
  norm_num

/-- The CFL 1/2 hypothesis of the bounds theorem cannot be replaced by CFL 2: the step leaves `[0, 1]`. -/
example : step (N := 2) 1 2 jump 0 < 0 := by
  rw [jump_step]
  norm_num

end CFDLean.Burgers.StabilityControls
