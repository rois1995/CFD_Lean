import CFDLean.Papers.JST1.Euler.State
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Statements of item 13 (P3): `prop:defect` (lines 162-168, proof 897-907); its first sentence is P2-6.2. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- P3-13.1 (exact production of a pair term): if `Φ(w) = F(u(w))·E` has derivative `B(w)` on the straight path
`w(s) = w_i + s [w]`, continuous along it, then `Φ(w_k) - Φ(w_i) = ∫_0^1 B(w(s)) [w] ds` and the production is
`[w] · ∫_0^1 B(w(s)) [w] ds`, with no remainder. -/
def P3_13_1 : Prop :=
  ∀ (κ : Type) [Fintype κ] (Φ : (κ → ℝ) → (κ → ℝ)) (B : (κ → ℝ) → (κ → ℝ) →L[ℝ] (κ → ℝ)) (wi wk : κ → ℝ),
    (∀ s ∈ Set.Icc (0 : ℝ) 1, HasFDerivAt Φ (B (wi + s • (wk - wi))) (wi + s • (wk - wi))) →
    ContinuousOn (fun s : ℝ => B (wi + s • (wk - wi)) (wk - wi)) (Set.Icc 0 1) →
    Φ wk - Φ wi = ∫ s in (0 : ℝ)..1, B (wi + s • (wk - wi)) (wk - wi) ∧
    pairF (wk - wi) (Φ wk - Φ wi) = ∫ s in (0 : ℝ)..1, pairF (wk - wi) (B (wi + s • (wk - wi)) (wk - wi))

/-- Sound speed `c = √(γ p/ρ)`. -/
def soundSpeed {d : ℕ} (g : Gas) (U : State d) : ℝ := Real.sqrt (g.γ * pressure g U / rho U)

/-- P3-13.2 (Euler, both signs): at an admissible state with `|v·E| < c|E|`, arbitrarily close admissible states
give the pair term `(F_k - F_i)·E` a positive production, and others a negative one. -/
def P3_13_2 : Prop :=
  ∀ (d : ℕ) (g : Gas) (U : State d) (E : Vec d), Admissible g U →
    |Num.dot (vel U) E| < soundSpeed g U * len E → ∀ ε > 0,
    (∃ Uk : State d, Admissible g Uk ∧ ‖Uk - U‖ < ε ∧
      0 < pairF (entropyVars g Uk - entropyVars g U) (physFlux g Uk E - physFlux g U E)) ∧
    (∃ Uk : State d, Admissible g Uk ∧ ‖Uk - U‖ < ε ∧
      pairF (entropyVars g Uk - entropyVars g U) (physFlux g Uk E - physFlux g U E) < 0)

end CFDLean.JST1.Spec
