import CFDLean.Papers.JST1.Proofs.Simplex
import CFDLean.Papers.JST1.Spec.Item5

noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

/-- A vector is fixed by its dot products with the edges `x_a - x_0`: `u = Σ_a (u·(x_a - x_0)) g_a`. -/
theorem vec_expand {d : ℕ} (T : Simplex d) (h : T.Nondeg) (u : Vec d) :
    u = ∑ a, Num.dot u (T.x a - T.x 0) • T.grad a := by
  obtain ⟨-, -, hI, -, -⟩ := p1_5_1 d T h
  have hs := grad_sum T
  funext α
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : u α = ∑ a, T.grad a α * Num.dot (T.x a) u := by
    have h1 : u α = ∑ β, (1 : Matrix (Fin d) (Fin d) ℝ) α β * u β := by
      simp [Matrix.one_apply]
    rw [h1, ← hI]
    simp only [Matrix.sum_apply, outer, Finset.sum_mul, Num.dot, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e0 : ∑ a, T.grad a α * Num.dot (T.x 0) u = 0 := by
    rw [← Finset.sum_mul]
    have := congrFun hs α
    simp only [Finset.sum_apply, Pi.zero_apply] at this
    rw [this, zero_mul]
  rw [e1, ← sub_zero (∑ a, T.grad a α * Num.dot (T.x a) u), ← e0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : Num.dot u (T.x a - T.x 0) = Num.dot (T.x a) u - Num.dot (T.x 0) u := by
    simp only [Num.dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [this]; ring

/-- Uniqueness form: equal edge dot products give equal vectors. -/
theorem vec_eq_of_dots {d : ℕ} (T : Simplex d) (h : T.Nondeg) (u v : Vec d)
    (huv : ∀ a, Num.dot u (T.x a - T.x 0) = Num.dot v (T.x a - T.x 0)) : u = v := by
  rw [vec_expand T h u, vec_expand T h v]
  simp only [huv]

end CFDLean.JST1.Proofs
