import CFDLean.Discrete.Periodic.TotalVariation
import Mathlib.Analysis.Convex.Function

/-! Burgers B2-B, generic part: the set of states between two bounds is convex, the periodic total variation is a
convex functional, and the total sum is a linear functional. These are the inputs of the SSP composition results. -/
noncomputable section
namespace CFDLean.Scalar.FiniteVolume

open Periodic
open scoped BigOperators

variable {I : Type*}

/-- Cell functions with `m ≤ u_j ≤ M` in every cell. -/
def boundedStates (m M : ℝ) : Set (I → ℝ) := {u | ∀ j, m ≤ u j ∧ u j ≤ M}

/-- B2-B: bounded states form a convex set. -/
theorem boundedStates_convex (m M : ℝ) : Convex ℝ (boundedStates (I := I) m M) := by
  intro a ha b hb s t hs ht hst j
  have h1 := ha j
  have h2 := hb j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have em : s * m + t * m = m := by rw [← add_mul, hst, one_mul]
  have eM : s * M + t * M = M := by rw [← add_mul, hst, one_mul]
  constructor <;> linarith [mul_le_mul_of_nonneg_left h1.1 hs, mul_le_mul_of_nonneg_left h2.1 ht,
    mul_le_mul_of_nonneg_left h1.2 hs, mul_le_mul_of_nonneg_left h2.2 ht]

/-- B2-B: the periodic total variation is convex on every convex set of states. -/
theorem totalVariation_convexOn [Fintype I] (g : Grid I) (S : Set (I → ℝ)) (hS : Convex ℝ S) :
    ConvexOn ℝ S (totalVariation g) := by
  refine ⟨hS, fun a _ b _ s t hs ht _ => ?_⟩
  simp only [totalVariation, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have e : s * a (g.next i) + t * b (g.next i) - (s * a i + t * b i) =
      s * (a (g.next i) - a i) + t * (b (g.next i) - b i) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]

/-- The total sum of the cell values as a linear functional. -/
def totalSum [Fintype I] : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i

theorem totalSum_apply [Fintype I] (u : I → ℝ) : totalSum u = ∑ i, u i := by
  simp [totalSum]

end CFDLean.Scalar.FiniteVolume
