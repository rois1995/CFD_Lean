import CFDLean.Schemes.Burgers.Rusanov
import CFDLean.Discrete.Periodic.Conservation
import CFDLean.Time.ForwardEuler

noncomputable section
namespace CFDLean.Burgers.Schemes.RusanovForwardEuler

open CFDLean.Burgers
open CFDLean.Burgers.Core
open CFDLean.Burgers.FiniteVolume
open CFDLean.Burgers.Time
open scoped BigOperators

variable {N : ℕ} [NeZero N]

def grid : PeriodicGrid (ZMod N) := zmodGrid N

def semidiscrete (dx : ℝ) : (ZMod N → ℝ) → ZMod N → ℝ :=
  rhs (grid (N := N)) dx Rusanov.numericalFlux

def step (dx dt : ℝ) (u : ZMod N → ℝ) : ZMod N → ℝ :=
  Time.step dt (semidiscrete (N := N) dx) u

theorem semidiscrete_constant (dx c : ℝ) :
    semidiscrete (N := N) dx (fun _ => c) = fun _ => 0 := by
  funext i
  exact rhs_constant (grid (N := N)) dx c law Rusanov.numericalFlux Rusanov.consistent i

theorem step_preserves_constant (dx dt c : ℝ) :
    step (N := N) dx dt (fun _ => c) = fun _ => c :=
  Time.step_constant dt (semidiscrete (N := N) dx) c
    (semidiscrete_constant (N := N) dx c)

theorem semidiscrete_sum_zero (dx : ℝ) (hdx : dx ≠ 0) (u : ZMod N → ℝ) :
    ∑ i, semidiscrete (N := N) dx u i = 0 :=
  rhs_sum_zero (grid (N := N)) dx hdx Rusanov.numericalFlux u

theorem step_preserves_sum (dx dt : ℝ) (hdx : dx ≠ 0) (u : ZMod N → ℝ) :
    ∑ i, step (N := N) dx dt u i = ∑ i, u i :=
  Time.step_sum dt (semidiscrete (N := N) dx) u
    (semidiscrete_sum_zero (N := N) dx hdx u)

theorem step_preserves_integral (dx dt : ℝ) (hdx : dx ≠ 0) (u : ZMod N → ℝ) :
    dx * ∑ i, step (N := N) dx dt u i = dx * ∑ i, u i := by
  rw [step_preserves_sum (N := N) dx dt hdx u]

end CFDLean.Burgers.Schemes.RusanovForwardEuler
