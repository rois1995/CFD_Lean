import CFDLean.Schemes.Scalar.NumericalFlux
import Mathlib.Tactic

/-! Burgers B3-K: the Lipschitz certificate of a two-point flux on states between two bounds. It is separate from the
evaluator and from the consistency and monotonicity certificates. -/
noncomputable section
namespace CFDLean.Scalar

/-- Lipschitz certificate of a two-point flux on states between m and M, one constant per argument. -/
def LipschitzOnBounds (nf : NumericalFlux) (m M KL KR : ℝ) : Prop :=
  (∀ a a' b, m ≤ a → a ≤ M → m ≤ a' → a' ≤ M → m ≤ b → b ≤ M →
    |nf.eval a b - nf.eval a' b| ≤ KL * |a - a'|) ∧
  (∀ a b b', m ≤ a → a ≤ M → m ≤ b → b ≤ M → m ≤ b' → b' ≤ M →
    |nf.eval a b - nf.eval a b'| ≤ KR * |b - b'|)

/-- A Lipschitz certificate on a nondegenerate interval has nonnegative constants. -/
theorem LipschitzOnBounds.nonneg {nf : NumericalFlux} {m M KL KR : ℝ} (h : LipschitzOnBounds nf m M KL KR)
    (hmM : m < M) : 0 ≤ KL ∧ 0 ≤ KR := by
  have hpos : 0 < |M - m| := abs_pos.mpr (sub_ne_zero.mpr hmM.ne')
  have h1 := h.1 M m m hmM.le le_rfl le_rfl hmM.le le_rfl hmM.le
  have h2 := h.2 m M m le_rfl hmM.le hmM.le le_rfl le_rfl hmM.le
  exact ⟨le_of_mul_le_mul_right (by rw [zero_mul]; exact (abs_nonneg _).trans h1) hpos,
    le_of_mul_le_mul_right (by rw [zero_mul]; exact (abs_nonneg _).trans h2) hpos⟩

end CFDLean.Scalar
