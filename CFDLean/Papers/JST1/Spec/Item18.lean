import CFDLean.Papers.JST1.Spec.Item10
set_option cleanup.letToHave false -- keep the `let` binders of the statements (as P1-P3)

/-! Statements of item 18 (P4): `lem:sstentropy` (lines 395-407, proof 1115-1121), the Hessian form ("its Hessian is
positive semidefinite with null space `span{e_E + e_k, e_ω}`"; the first-order form is P2-10.3). The Hessian is the
Fréchet derivative of `fderiv η0`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- P4-18.1 (proof of `lem:sstentropy`: "`∇²η` is positive definite on admissible states"): at an admissible Euler
state the entropy `η = -ρ s/(γ-1)` has a second derivative `H`, and `H δ δ > 0` for every `δ ≠ 0`. -/
def P4_18_1 : Prop :=
  ∀ (d : ℕ) (g : Gas) (u : State d), Admissible g u →
    ∃ H : State d →L[ℝ] State d →L[ℝ] ℝ, HasFDerivAt (fderiv ℝ (entropyFun g)) H u ∧
      ∀ δ : State d, δ ≠ 0 → 0 < H δ δ

/-- P4-18.2 (`lem:sstentropy`, Hessian form): at an admissible SST state `η0` has a second derivative `H`; it is
positive semidefinite, and its null space `{δ : H δ = 0}` (equivalently `{δ : H δ δ = 0}`) is
`span{e_E + e_k, e_ω}`. -/
def P4_18_2 : Prop :=
  ∀ (d : ℕ) (g : Gas) (U : SState d), SAdmissible g U →
    ∃ H : SState d →L[ℝ] SState d →L[ℝ] ℝ, HasFDerivAt (fderiv ℝ (eta0 g)) H U ∧
      (∀ δ, 0 ≤ H δ δ) ∧
      (∀ δ, H δ = 0 ↔ ∃ a b : ℝ, δ = a • nullE + b • nullW) ∧
      (∀ δ, H δ δ = 0 ↔ ∃ a b : ℝ, δ = a • nullE + b • nullW)

end CFDLean.JST1.Spec
