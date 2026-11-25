import CFDLean.Papers.JST1.Euler.State
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Frozen statements of item 1: `lem:eps2` (paper1.tex lines 247-270). Each `P1_1_x` is a `Prop`; the proofs
bind to these names in `specifications/P1-results.json`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology
namespace CFDLean.JST1.Spec

/-- P1-1.0: `w` is the gradient of `U = -ρ s/(γ-1)` at admissible states. -/
def P1_1_0 : Prop :=
  ∀ (d : ℕ) (g : Gas) (U : State d), Admissible g U →
    HasFDerivAt (entropyFun g) (pairCLM (entropyVars g U)) U

/-- P1-1.1: the thermodynamic pencil, pointwise, with equality cases. -/
def P1_1_1 : Prop :=
  ∀ γ : ℝ, 1 < γ →
    (∀ a b : ℝ, lamLow γ * thermoQ γ a b ≤ thermoQt γ a b ∧ thermoQt γ a b ≤ lamHigh γ * thermoQ γ a b) ∧
    (∃ a b : ℝ, (a, b) ≠ (0, 0) ∧ thermoQt γ a b = lamLow γ * thermoQ γ a b) ∧
    (∃ a b : ℝ, (a, b) ≠ (0, 0) ∧ thermoQt γ a b = lamHigh γ * thermoQ γ a b)

/-- P1-1.2: `λ_γ [w]·[u] ≤ [w]·[ũ] ≤ Λ_γ [w]·[u]` for admissible states. -/
def P1_1_2 : Prop :=
  ∀ (d : ℕ) (g : Gas) (Ui Uk : State d), Admissible g Ui → Admissible g Uk →
    let dw := entropyVars g Uk - entropyVars g Ui
    lamLow g.γ * pairF dw (Uk - Ui) ≤ pairF dw (enthalpyState g Uk - enthalpyState g Ui) ∧
    pairF dw (enthalpyState g Uk - enthalpyState g Ui) ≤ lamHigh g.γ * pairF dw (Uk - Ui)

/-- P1-1.3: `[w]·[u] ≥ 0` (convexity of the entropy). -/
def P1_1_3 : Prop :=
  ∀ (d : ℕ) (g : Gas) (Ui Uk : State d), Admissible g Ui → Admissible g Uk →
    0 ≤ pairF (entropyVars g Uk - entropyVars g Ui) (Uk - Ui)

/-- P1-1.4: the constants. -/
def P1_1_4 : Prop :=
  (∀ γ : ℝ, 1 < γ → 3 / 4 < lamLow γ ∧ lamLow γ < 1 ∧ 1 < lamHigh γ) ∧
  StrictAntiOn lamLow (Set.Ioi 1) ∧
  Tendsto lamLow (𝓝[>] 1) (𝓝 1) ∧ Tendsto lamLow atTop (𝓝 (3 / 4)) ∧
  (8258 / 10000 : ℝ) < lamLow (14 / 10) ∧ lamLow (14 / 10) < 8259 / 10000

/-- P1-1.5: the second-difference flux `λ ε2 (ũ_i - ũ_k)` produces at most `-λ_γ ε2 λ [w]·[u] ≤ 0`. -/
def P1_1_5 : Prop :=
  ∀ (d : ℕ) (g : Gas) (Ui Uk : State d) (lam eps2 : ℝ), Admissible g Ui → Admissible g Uk →
    0 ≤ lam → 0 ≤ eps2 →
    let dw := entropyVars g Uk - entropyVars g Ui
    let d2 := (lam * eps2) • (enthalpyState g Ui - enthalpyState g Uk)
    pairF dw d2 = -(eps2 * lam) * pairF dw (enthalpyState g Uk - enthalpyState g Ui) ∧
    pairF dw d2 ≤ -(lamLow g.γ) * eps2 * lam * pairF dw (Uk - Ui) ∧
    -(lamLow g.γ) * eps2 * lam * pairF dw (Uk - Ui) ≤ 0

/-- P1-1.6: best constants for two states (no larger lower and no smaller upper constant holds). -/
def P1_1_6 : Prop :=
  ∀ (d : ℕ) (g : Gas) (ε : ℝ), 0 < ε →
    (∃ Ui Uk : State d, Admissible g Ui ∧ Admissible g Uk ∧
      0 < pairF (entropyVars g Uk - entropyVars g Ui) (Uk - Ui) ∧
      pairF (entropyVars g Uk - entropyVars g Ui) (enthalpyState g Uk - enthalpyState g Ui) <
        (lamLow g.γ + ε) * pairF (entropyVars g Uk - entropyVars g Ui) (Uk - Ui)) ∧
    (∃ Ui Uk : State d, Admissible g Ui ∧ Admissible g Uk ∧
      0 < pairF (entropyVars g Uk - entropyVars g Ui) (Uk - Ui) ∧
      (lamHigh g.γ - ε) * pairF (entropyVars g Uk - entropyVars g Ui) (Uk - Ui) <
        pairF (entropyVars g Uk - entropyVars g Ui) (enthalpyState g Uk - enthalpyState g Ui))

end CFDLean.JST1.Spec
