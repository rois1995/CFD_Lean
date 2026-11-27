import CFDLean.Schemes.Burgers.RusanovForwardEuler
import Mathlib.Tactic.NormNum

/-!
# Orientation controls for the assembled B0 scheme

The trusted B0 statements quantify over any periodic successor `next : I ≃ I`, so the comparator does not show that
the assembled `ZMod N` grid steps to `i + 1`. These controls state the assembled update in explicit index form and fix
its orientation with an exact three-cell example. They add no promised result.
-/

noncomputable section
namespace CFDLean.Burgers.GridControls

open CFDLean.Periodic
open CFDLean.Scalar.FiniteVolume
open CFDLean.Burgers.Schemes.RusanovForwardEuler

variable {N : ℕ} [NeZero N]

theorem grid_next (i : ZMod N) : (grid (N := N)).next i = i + 1 := rfl

theorem grid_prev (i : ZMod N) : (grid (N := N)).prev i = i - 1 := by
  simp [Grid.prev, grid, zmodGrid, sub_eq_add_neg]

/-- The assembled B0 update in explicit index form. -/
theorem step_apply (dx dt : ℝ) (u : ZMod N → ℝ) (i : ZMod N) :
    step (N := N) dx dt u i =
      u i + dt * (-(Rusanov.eval (u i) (u (i + 1)) - Rusanov.eval (u (i - 1)) (u i)) / dx) := by
  have h : (grid (N := N)).next ((grid (N := N)).prev i) = i := Grid.next_prev _ i
  simp only [step, Time.ForwardEuler.step, semidiscrete, rhs, interfaceFlux, h]
  rw [grid_next, grid_prev]
  rfl

/-- A unit mass in cell 0 moves to cell 1 (to the right, since `u > 0`), with Rusanov dissipation into cell 2.
After one step the cells hold `(0, 3/4, 1/4)`; the opposite orientation would give `(0, 1/4, 3/4)`. -/
def pulse : ZMod 3 → ℝ := fun i => if i = 0 then 1 else 0

example : step (N := 3) 1 1 pulse 0 = 0 := by
  rw [step_apply]
  norm_num [pulse, Rusanov.eval, Rusanov.waveSpeed, physicalFlux, (by decide : (-1 : ZMod 3) ≠ 0)]

example : step (N := 3) 1 1 pulse 1 = 3 / 4 := by
  rw [step_apply]
  norm_num [pulse, Rusanov.eval, Rusanov.waveSpeed, physicalFlux, (by decide : (2 : ZMod 3) ≠ 0)]

example : step (N := 3) 1 1 pulse 2 = 1 / 4 := by
  rw [step_apply, show (2 : ZMod 3) + 1 = 0 from rfl, show (2 : ZMod 3) - 1 = 1 from rfl]
  norm_num [pulse, Rusanov.eval, Rusanov.waveSpeed, physicalFlux, (by decide : (2 : ZMod 3) ≠ 0),
    (by decide : (1 : ZMod 3) ≠ 0)]

end CFDLean.Burgers.GridControls
