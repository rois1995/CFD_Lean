import CFDLean.Papers.JST1.Euler.IsmailRoe
set_option cleanup.letToHave false -- keep the `let` binders of the statements (as P1-P4)

/-! Statements of item 19 (P5): the smoothness of the Ismail-Roe flux near the diagonal, which `prop:consistency`(b)
(line 285, proof line 952: "a symmetric, consistent, smooth two-point flux") needs and P4-16.2 assumes
(`PAPER_GAPS.md` G6). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology Asymptotics
namespace CFDLean.JST1.Spec

/-- P5-19.1 (G6): the logarithmic mean (`logMean a a = a` on the diagonal, `(b - a)/(ln b - ln a)` off it) is `Cⁿ`
for every `n` on the open quadrant `a > 0, b > 0`, across the diagonal `a = b` despite the case split. -/
def P5_19_1 : Prop :=
  ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry logMean) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))

/-- P5-19.2 (G6): the set of admissible states (`ρ > 0`, `p > 0`) is open, and for every gas and every vector `y` the
Ismail-Roe flux `(U_a, U_b) ↦ F^IR(U_a, U_b; y)` is `Cⁿ` for every `n` on (admissible) × (admissible), the diagonal
included. -/
def P5_19_2 : Prop :=
  ∀ (d : ℕ) (g : Gas) (y : Vec d),
    IsOpen {U : State d | Admissible g U} ∧
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry fun Ua Ub : State d => ismailRoe g Ua Ub y)
      ({U : State d | Admissible g U} ×ˢ {U : State d | Admissible g U})

/-- P5-19.3 (`prop:consistency`(b), last clause, for the scheme's flux; from P4-16.2 with P5-19.2 and the symmetry and
consistency of P1-2.x, and the linearity in `y`): at every admissible state `u0` there is one constant `C` such that,
for `(u_i, u_k)` near `(u0, u0)` and every vector `y` (so for every face vector `n_ik`), the Ismail-Roe flux differs from
the mean of the Euler fluxes by at most `C |y| |u_k - u_i|²` (sup norms). On a compact set of admissible states one
constant then holds for all pairs close enough to the diagonal (not stated). -/
def P5_19_3 : Prop :=
  ∀ (d : ℕ) (g : Gas) (u0 : State d), Admissible g u0 →
    ∃ C : ℝ, ∀ᶠ p : State d × State d in 𝓝 (u0, u0), ∀ y : Vec d,
      ‖ismailRoe g p.1 p.2 y - (1 / 2 : ℝ) • (physFlux g p.1 y + physFlux g p.2 y)‖ ≤ C * ‖y‖ * ‖p.2 - p.1‖ ^ 2

end CFDLean.JST1.Spec
