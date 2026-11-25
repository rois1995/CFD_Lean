import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field

noncomputable section
namespace CFDLean.Burgers.Time

open scoped BigOperators

variable {I : Type*}

def step (dt : ℝ) (L : (I → ℝ) → I → ℝ) (u : I → ℝ) : I → ℝ :=
  fun i => u i + dt * L u i

theorem step_zero_rhs (dt : ℝ) (L : (I → ℝ) → I → ℝ) (u : I → ℝ)
    (hL : L u = fun _ => 0) :
    step dt L u = u := by
  funext i
  simp [step, hL]

theorem step_constant (dt : ℝ) (L : (I → ℝ) → I → ℝ) (c : ℝ)
    (hL : L (fun _ => c) = fun _ => 0) :
    step dt L (fun _ => c) = fun _ => c :=
  step_zero_rhs dt L (fun _ => c) hL

theorem step_sum [Fintype I] (dt : ℝ) (L : (I → ℝ) → I → ℝ) (u : I → ℝ)
    (hL : ∑ i, L u i = 0) :
    ∑ i, step dt L u i = ∑ i, u i := by
  simp only [step, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hL]
  simp

end CFDLean.Burgers.Time
