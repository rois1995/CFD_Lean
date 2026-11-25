import CFDLean.Num.Basic

/-! Exact production of a pair term by the fundamental theorem of calculus (P3-13.1).

MC-N: proof moved from JST_Paper_Lean `Paper1/Proofs/Item13.lean`. -/
noncomputable section
open scoped BigOperators
namespace CFDLean.Num.Internal

namespace Def13

theorem pairF_eq_CLM {κ : Type} [Fintype κ] (w x : κ → ℝ) : pairF w x = pairCLM w x := by
  simp [pairCLM, pairF]

end Def13

open Def13 in
/-- MC-N.P3-13.1 (JST `Paper1.Spec.P3_13_1`, proof `Paper1.Proofs.p3_13_1`). P3-13.1 (exact production of a pair term): if `Φ(w) = F(u(w))·E` has derivative `B(w)` on the straight path `w(s) = w_i + s [w]`, continuous along it, then `Φ(w_k) - Φ(w_i) = ∫_0^1 B(w(s)) [w] ds` and the production is `[w] · ∫_0^1 B(w(s)) [w] ds`, with no remainder. -/
theorem _root_.CFDLean.Num.pair_production_integral :
    ∀ (κ : Type) [Fintype κ] (Φ : (κ → ℝ) → (κ → ℝ)) (B : (κ → ℝ) → (κ → ℝ) →L[ℝ] (κ → ℝ)) (wi wk : κ → ℝ),
      (∀ s ∈ Set.Icc (0 : ℝ) 1, HasFDerivAt Φ (B (wi + s • (wk - wi))) (wi + s • (wk - wi))) →
      ContinuousOn (fun s : ℝ => B (wi + s • (wk - wi)) (wk - wi)) (Set.Icc 0 1) →
      Φ wk - Φ wi = ∫ s in (0 : ℝ)..1, B (wi + s • (wk - wi)) (wk - wi) ∧
      pairF (wk - wi) (Φ wk - Φ wi) = ∫ s in (0 : ℝ)..1, pairF (wk - wi) (B (wi + s • (wk - wi)) (wk - wi)) := by
  intro κ _ Φ B wi wk hΦ hB
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => wi + s • (wk - wi)) (wk - wi) s := by
    intro s
    have := ((hasDerivAt_id s).smul_const (wk - wi)).const_add wi
    simpa using this
  have hI : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hint : IntervalIntegrable (fun s : ℝ => B (wi + s • (wk - wi)) (wk - wi)) MeasureTheory.volume 0 1 :=
    (hI ▸ hB).intervalIntegrable
  have hftc : ∫ s in (0 : ℝ)..1, B (wi + s • (wk - wi)) (wk - wi) = Φ wk - Φ wi := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => Φ (wi + s • (wk - wi))) (a := 0) (b := 1)
      (fun s hs => (hΦ s (hI ▸ hs)).comp_hasDerivAt s (hpath s)) hint
    simpa using this
  refine ⟨hftc.symm, ?_⟩
  rw [← hftc, pairF_eq_CLM, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  simp only [pairF_eq_CLM]

end CFDLean.Num.Internal
