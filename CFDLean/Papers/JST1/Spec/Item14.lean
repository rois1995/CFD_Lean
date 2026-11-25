import CFDLean.Papers.JST1.Scheme.Complete
import CFDLean.Papers.JST1.Spec.Addendum2
import CFDLean.Papers.JST1.Euler.Boundary
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Statements of item 14 (P3): `thm:complete` (lines 530-548, proof 1165-1177) for the complete scheme of
`CFDLean/Papers/JST1/Scheme/Complete.lean`, on a facet-balanced weighted simplex mesh (simplex meshes: P2-6.3; mixed meshes:
P3-11.1-11.6). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec
open CFDLean.JST1.Scheme

/-- Hypotheses of the complete scheme: valid facet-balanced mesh with boundary facets; the face points lie on boundary
facets with (H1), (H2) and `φ = 0` off their facet; projected states `w(ũ_q) = Σ_k φ_qk w_k`; symmetric non-negative
dissipation coefficients; `μ, κ ≥ 0`, `R > 0` per cell; an orthogonal projector with `P g = g` at walls. -/
def SchemeHyp {ι C Q : Type} [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C] [Fintype Q] {d : ℕ}
    (S : Data ι C Q d) (bd : C × Fin (d + 1) → Bool) (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ)
    (u : ι → State d) : Prop :=
  S.M.Valid ∧ 1 ≤ d ∧ d ≤ 3 ∧ S.M.FacetBalanced bd ∧
  (∀ i, Admissible S.g (u i)) ∧ (∀ q, Admissible S.g (S.ut q)) ∧
  (∀ q, bd (fq q) = true) ∧ (∀ q k, k ∉ S.M.facetNodes (fq q) → S.φ q k = 0) ∧
  (∀ p, bd p = true → ∀ i ∈ S.M.facetNodes p,
      (∑ q, if fq q = p then aq q * S.φ q i else 0) = 1 / (d : ℝ)) ∧
  (∀ p, bd p = true → ∀ i ∈ S.M.facetNodes p, ∀ k ∈ S.M.facetNodes p,
      (∑ q, if fq q = p then aq q * S.φ q i * S.φ q k else 0) = (1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) ∧
  (∀ q, S.N q = aq q • S.M.areaVec (fq q)) ∧ (∀ q, ∑ k, S.φ q k = 1) ∧
  (∀ q, entropyVars S.g (S.ut q) = ∑ k, S.φ q k • entropyVars S.g (u k)) ∧
  (∀ i k, S.lam k i = S.lam i k ∧ S.eps2 k i = S.eps2 i k ∧ S.eps4 k i = S.eps4 i k) ∧
  (∀ i k, 0 ≤ S.lam i k ∧ 0 ≤ S.eps2 i k ∧ 0 ≤ S.eps4 i k) ∧
  (∀ T, 0 ≤ (S.Pv T).μ ∧ 0 ≤ (S.Pv T).κ ∧ 0 < (S.Pv T).R) ∧
  S.P.transpose = S.P ∧ S.P * S.P = S.P ∧ S.P.mulVec S.gw = S.gw

/-- P3-14.1 (`thm:complete`, entropy balance): the rate `Σ_i w_i · (V du/dt)_i` of the complete scheme is exactly
`B + Π^(2) + Π^(4) - Σ_T ω_T (D^gal_T - Π^w_T) + (wall flux)`, with `Π^(2) ≤ 0`; and for `c ≥ 1` every element term
satisfies `D^gal_T - Π^w_T ≥ (1 - 1/c) D^gal_T ≥ 0`. The conservative part: the pair fluxes are antisymmetric.
Laminar flow and SA (`μ_t ≥ 0` inside `Pv`) are this identity; it is stated for the rate `Σ w·(V du/dt)` (the time
derivative form is P3-14.3 for SST). Not all hypotheses of `SchemeHyp` are needed (H2 is used only for linear
exactness); `walls` is not tied to `bd` (a harmless generalisation). -/
def P3_14_1 : Prop :=
  ∀ (ι C Q : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C] [Fintype Q] (d : ℕ)
    (S : Data ι C Q d) (bd : C × Fin (d + 1) → Bool) (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ) (u : ι → State d),
    SchemeHyp S bd fq aq u →
    (∑ i, pairF (w S u i) (resid S u i)) =
      Bterm S + Pi2 S u + Pi4 S u - (∑ T, S.M.ω T * (Dg S u T - Pw S u T)) + wallFlux S u ∧
    Pi2 S u ≤ 0 ∧
    (1 ≤ S.c → ∀ T, (1 - 1 / S.c) * Dg S u T ≤ Dg S u T - Pw S u T ∧ 0 ≤ (1 - 1 / S.c) * Dg S u T) ∧
    (∀ i k, central S u k i + diss2 S u k i - diss4 S u k i = -(central S u i k + diss2 S u i k - diss4 S u i k))

/-- P3-14.2 (boundary term): if every face point is a slip or no-slip wall point (pressure flux) or a far-field point whose
flux is entropy stable against a ghost state, `B` is at most the sum of the ghost entropy fluxes of the far-field
points (slip points contribute zero). -/
def P3_14_2 : Prop :=
  ∀ (ι C Q : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype Q] (d : ℕ) (S : Data ι C Q d)
    (slip : Q → Bool) (ug : Q → State d),
    (∀ q, Admissible S.g (S.ut q)) →
    (∀ q, slip q = true → S.Fs q = pressFlux S.g (S.ut q) (S.N q)) →
    (∀ q, slip q = false → pairF (entropyVars S.g (ug q) - entropyVars S.g (S.ut q)) (S.Fs q) ≤
      Num.dot (fluxPot (ug q) - fluxPot (S.ut q)) (S.N q)) →
    Bterm S ≤ ∑ q, if slip q then 0 else
      Num.dot (fluxPot (ug q)) (S.N q) - pairF (entropyVars S.g (ug q)) (S.Fs q)

/-- P3-14.3 (`thm:complete` for SST, chained with P2-10.8c): for SST trajectories whose hat residual is minus the
residual of the complete scheme on the hat states (with `μ + μ_t` in `Pv`) plus `(X - R_k) e_E`, under (M1)-(M5) as
in P2-10.8, `Σ D_t = Σ 2βVP*` and (W_t) for the element terms of the scheme, the rate `d/dt Σ V η0` exists and is at
most `B + wall flux + Π^(2) + Π^(4) - Σ_T ω_T (D^gal_T - D_t,T - Π^w_T)` minus the non-negative node terms.
`Vv`, `Dt` are free inputs tied only by the stated hypotheses; `μ + μ_t` in `Pv` is the user's choice of data. -/
def P3_14_3 : Prop :=
  ∀ (ι C Q : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C] [Fintype Q] (d : ℕ)
    (S : Data ι C Q d) (bd : C × Fin (d + 1) → Bool) (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ)
    (Ut : ι → ℝ → SState d) (Vv : ι → ℝ) (R : ι → SState d) (t : ℝ)
    (X Ck Bk Dh Sk Rrho Pst : ι → ℝ) (inD : ι → Bool) (kD : ℝ) (Dt : C → ℝ),
    let u : ι → State d := fun i => hatState (Ut i t)
    SchemeHyp S bd fq aq u →
    (∀ i, 0 < Vv i) → (∀ i, HasDerivAt (Ut i) (-(Vv i)⁻¹ • R i) t) →
    let β2 : ι → ℝ := fun i => -(entropyVars S.g (u i) .energy)
    let Rk : ι → ℝ := fun i => if inD i then kD * Rrho i else Ck i + Bk i + Dh i - Vv i * Sk i
    (∀ i, hatState (R i) = -resid S u i + (X i - Rk i) • eE) → (∀ i, 0 ≤ Pst i) →
    (∀ i, inD i = false → X i = Ck i + Bk i + Dh i) →
    (∀ i, inD i = false → Sk i ≤ Pst i) →
    (∀ i, inD i = true → X i - kD * Rrho i ≤ 0) →
    (∑ T, S.M.ω T * Dt T) = ∑ i, β2 i * Vv i * Pst i →
    (∀ T, Pw S u T ≤ Dg S u T - Dt T) →
    ∃ r : ℝ, HasDerivAt (fun s => ∑ i, Vv i * eta0 S.g (Ut i s)) r t ∧
      r ≤ Bterm S + wallFlux S u + Pi2 S u + Pi4 S u - (∑ T, S.M.ω T * (Dg S u T - Dt T - Pw S u T)) -
        (∑ i, if inD i then 0 else β2 i * Vv i * (Pst i - Sk i)) - (∑ i, if inD i then β2 i * Vv i * Pst i else 0)

end CFDLean.JST1.Spec
