import CFDLean.Burgers.Flux.Rusanov
import CFDLean.Burgers.FiniteVolume.Conservation
import CFDLean.Burgers.Time.ForwardEuler

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
  rhs grid dx Rusanov.numericalFlux

def step (dx dt : ℝ) (u : ZMod N → ℝ) : ZMod N → ℝ :=
  Time.step dt (semidiscrete dx) u

theorem semidiscrete_constant (dx c : ℝ) :
    semidiscrete dx (fun _ => c) = fun _ => 0 := by
  funext i
  exact rhs_constant grid dx c law Rusanov.numericalFlux Rusanov.consistent i

theorem step_preserves_constant (dx dt c : ℝ) :
    step dx dt (fun _ => c) = fun _ => c :=
  Time.step_constant dt (semidiscrete dx) c (semidiscrete_constant dx c)

theorem semidiscrete_sum_zero (dx : ℝ) (hdx : dx ≠ 0) (u : ZMod N → ℝ) :
    ∑ i, semidiscrete dx u i = 0 :=
  rhs_sum_zero grid dx hdx Rusanov.numericalFlux u

theorem step_preserves_sum (dx dt : ℝ) (hdx : dx ≠ 0) (u : ZMod N → ℝ) :
    ∑ i, step dx dt u i = ∑ i, u i :=
  Time.step_sum dt (semidiscrete dx) u (semidiscrete_sum_zero dx hdx u)

theorem step_preserves_integral (dx dt : ℝ) (hdx : dx ≠ 0) (u : ZMod N → ℝ) :
    dx * ∑ i, step dx dt u i = dx * ∑ i, u i := by
  rw [step_preserves_sum dx dt hdx u]

end CFDLean.Burgers.Schemes.RusanovForwardEuler
