import CFDLean.Num.Basic

/-! Logarithmic mean.

MC-N: definition moved verbatim from JST_Paper_Lean `NumCore/LogMean.lean`; P1-2.4 with its JST proof. -/
noncomputable section
namespace CFDLean.Num

/-- Logarithmic mean, with the diagonal value `a`. -/
def logMean (a b : ℝ) : ℝ := if a = b then a else (b - a) / (Real.log b - Real.log a)

end CFDLean.Num

namespace CFDLean.Num.Internal

/-- MC-N.P1-2.4 (JST `Paper1.Spec.P1_2_4`, proof `Paper1.Proofs.p1_2_4`). P1-2.4: log mean. -/
theorem _root_.CFDLean.Num.logMean_properties :
    ∀ a b : ℝ, 0 < a → 0 < b →
      logMean a b = logMean b a ∧ logMean a a = a ∧ 0 < logMean a b ∧
      b - a = logMean a b * (Real.log b - Real.log a) := by
  intro a b ha hb
  have key : ∀ x y : ℝ, 0 < x → 0 < y → x ≠ y → Real.log y - Real.log x ≠ 0 := by
    intro x y hx hy hxy h
    apply hxy
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) (by linarith)
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold logMean
    by_cases h : a = b
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
      rw [← neg_sub b a, ← neg_sub (Real.log b) (Real.log a), neg_div_neg_eq]
  · simp [logMean]
  · unfold logMean
    by_cases h : a = b
    · rw [ite_eq_left h]; exact ha
    · rw [ite_eq_right h]
      rcases lt_or_gt_of_ne h with hab | hab
      · apply div_pos (by linarith)
        have := Real.log_lt_log ha hab; linarith
      · apply div_pos_of_neg_of_neg (by linarith)
        have := Real.log_lt_log hb hab; linarith
  · unfold logMean
    by_cases h : a = b
    · subst h; simp
    · rw [ite_eq_right h, div_mul_cancel₀ _ (key a b ha hb h)]

end CFDLean.Num.Internal
