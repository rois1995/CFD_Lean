import CFDLean.Discrete.Periodic.Grid
import Mathlib.Tactic

/-! Burgers B1-V, B1-H, B1-X: total variation on a periodic grid, updates in incremental (Harten) form, and the two
generic stability lemmas of the incremental form. No numerical flux appears here. -/
noncomputable section
namespace CFDLean.Scalar.FiniteVolume

open Periodic
open scoped BigOperators

variable {I : Type*}

/-- Total variation of a cell function on a periodic grid: `Σ_i |u_{i+1} - u_i|`. -/
def totalVariation [Fintype I] (g : Grid I) (u : I → ℝ) : ℝ :=
  ∑ i, |u (g.next i) - u i|

/-- One-step update in incremental form. `C i` and `D i` are the coefficients of the interface between cell `i` and
cell `g.next i`: `v_i = u_i + C_i (u_{i+1} - u_i) - D_{i-1} (u_i - u_{i-1})`. -/
def incrementalUpdate (g : Grid I) (C D : I → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  u i + C i * (u (g.next i) - u i) - D (g.prev i) * (u i - u (g.prev i))

/-- B1-H (Harten): nonnegative interface coefficients with `C_i + D_i ≤ 1` do not increase the total variation. -/
theorem incrementalUpdate_totalVariation_le [Fintype I] (g : Grid I) (C D u : I → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hD : ∀ i, 0 ≤ D i) (hCD : ∀ i, C i + D i ≤ 1) :
    totalVariation g (incrementalUpdate g C D u) ≤ totalVariation g u := by
  have bound : ∀ i, |incrementalUpdate g C D u (g.next i) - incrementalUpdate g C D u i| ≤
      (1 - C i - D i) * |u (g.next i) - u i| + C (g.next i) * |u (g.next (g.next i)) - u (g.next i)|
        + D (g.prev i) * |u i - u (g.prev i)| := by
    intro i
    have key : incrementalUpdate g C D u (g.next i) - incrementalUpdate g C D u i =
        (1 - C i - D i) * (u (g.next i) - u i) + C (g.next i) * (u (g.next (g.next i)) - u (g.next i))
          + D (g.prev i) * (u i - u (g.prev i)) := by
      simp only [incrementalUpdate, g.prev_next]
      ring
    rw [key]
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hC _), abs_of_nonneg (hD _),
      abs_of_nonneg (by linarith [hCD i] : (0 : ℝ) ≤ 1 - C i - D i)]
  unfold totalVariation
  refine (Finset.sum_le_sum fun i _ => bound i).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    g.sum_next (fun i => C i * |u (g.next i) - u i|)]
  have h := g.sum_prev (fun i => D i * |u (g.next i) - u i|)
  simp only [g.next_prev] at h
  rw [h, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- B1-X: with `0 ≤ C_i`, `0 ≤ D_{i-1}` and `C_i + D_{i-1} ≤ 1` the updated value at `i` is a convex combination of
the old values at `i - 1`, `i`, `i + 1`, so it keeps every lower and upper bound of the old state. -/
theorem incrementalUpdate_bounds (g : Grid I) (C D u : I → ℝ) (m M : ℝ) (i : I)
    (hC : 0 ≤ C i) (hD : 0 ≤ D (g.prev i)) (hCD : C i + D (g.prev i) ≤ 1)
    (hm : ∀ j, m ≤ u j) (hM : ∀ j, u j ≤ M) :
    m ≤ incrementalUpdate g C D u i ∧ incrementalUpdate g C D u i ≤ M := by
  have e : incrementalUpdate g C D u i =
      (1 - C i - D (g.prev i)) * u i + C i * u (g.next i) + D (g.prev i) * u (g.prev i) := by
    simp only [incrementalUpdate]
    ring
  have h0 : 0 ≤ 1 - C i - D (g.prev i) := by linarith
  rw [e]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (hm i) h0, mul_le_mul_of_nonneg_left (hm (g.next i)) hC,
      mul_le_mul_of_nonneg_left (hm (g.prev i)) hD]
  · nlinarith [mul_le_mul_of_nonneg_left (hM i) h0, mul_le_mul_of_nonneg_left (hM (g.next i)) hC,
      mul_le_mul_of_nonneg_left (hM (g.prev i)) hD]

end CFDLean.Scalar.FiniteVolume
