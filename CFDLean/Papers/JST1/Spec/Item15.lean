import CFDLean.Papers.JST1.Spec.Item14
set_option cleanup.letToHave false -- keep the `let` binders of the statements (as P1-P3)

/-! Statements of item 15 (P4): `prop:wallJST` (lines 347-372, proof 1092-1113), scalar dissipation at weak walls.
The wall-normal model of the proof: nodes `y_s = 0` (wall), `y_k = h`, `y_2 = (1+r) h`; the profile is one component
of `ũ`; the wall node has boundary-only neighbours, all at `y = 0`, so the normal part of `L_s` is 0. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology Asymptotics
namespace CFDLean.JST1.Spec
open CFDLean.JST1.Scheme

/-- Wall-normal model: `L_k = (f(y_s) - f(y_k)) + (f(y_2) - f(y_k))` for the nodes `0, h, (1+r) h`. -/
def wnLk (f : ℝ → ℝ) (r h : ℝ) : ℝ := (f 0 - f h) + (f ((1 + r) * h) - f h)

/-- P4-15.1 (`prop:wallJST`(a)): for a `C³` profile, `L_k = (r-1) h f'(y_k) + ½(1+r²) h² f''(y_k) + O(h³)` as
`h → 0`; `L_k / h → (r-1) f'(0)` (first order if `r ≠ 1` and `f'(0) ≠ 0`, hence not a third difference), and
`L_k / h² → f''(0)` if `r = 1` (second order). The fourth-difference flux of the wall row is `ε4 λ (L_k - L_s)` with
`L_s = 0` (normal part) in the model. -/
def P4_15_1 : Prop :=
  ∀ (f : ℝ → ℝ) (r : ℝ), ContDiff ℝ 3 f →
    (fun h => wnLk f r h - ((r - 1) * h * deriv f h + (1 / 2) * (1 + r ^ 2) * h ^ 2 * deriv (deriv f) h))
      =O[𝓝 0] (fun h => h ^ 3) ∧
    Tendsto (fun h => wnLk f r h / h) (𝓝[≠] 0) (𝓝 ((r - 1) * deriv f 0)) ∧
    (r = 1 → Tendsto (fun h => wnLk f r h / h ^ 2) (𝓝[≠] 0) (𝓝 (deriv (deriv f) 0)))

/-- P4-15.2 (`prop:wallJST`(a), wall slip; trivial algebra): the one-node balance `ε4λ (L⁰_k + u_s) + σ u_s = 0` of the
tangential wall momentum `u_s` with the penalty stiffness `σ > 0` (`u_s` has coefficient `+1` in `L_k`, `L⁰_k` is the
rest) has the unique solution `u_s = -ϱ L⁰_k / (1 + ϱ)`, `ϱ = ε4λ/σ`; it is negative (opposite to the flow) if
`ε4λ > 0` and `L⁰_k > 0`; and for the linear no-slip profile `u = a y` with `a > 0`, `r > 1`, `h > 0`,
`L⁰_k = (u_2 - u_k) - u_k > 0`. The balance is the model of the proof, not derived from the scheme: in `resid` the
wall row receives `+diss4 s k = λε4 (L_s - L_k) = -λε4 L_k` (`L_s = 0`), and the penalty `-σ u_s`. -/
def P4_15_2 : Prop :=
  (∀ (e4l σ L0 : ℝ), 0 ≤ e4l → 0 < σ →
    (∀ us : ℝ, e4l * (L0 + us) + σ * us = 0 ↔ us = -((e4l / σ) * L0) / (1 + e4l / σ)) ∧
    (0 < e4l → 0 < L0 → -((e4l / σ) * L0) / (1 + e4l / σ) < 0)) ∧
  (∀ (a r h : ℝ), 0 < a → 1 < r → 0 < h → 0 < (a * ((1 + r) * h) - a * h) - a * h)

/-- P4-15.3 (`prop:wallJST`(b), trivial): the momentum rows of the second-difference flux of the scheme on the edge
`sk` are `λ ε2 (ρv_s - ρv_k)`, a difference with no power of `h`. The scaling `ε2 ρ c h / μ` of the paper ("a
scaling, not an estimate") is not stated. -/
def P4_15_3 : Prop :=
  ∀ (ι C Q : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype Q] (d : ℕ) (S : Data ι C Q d)
    (u : ι → State d) (s k : ι) (α : Fin d),
    diss2 S u s k (.momentum α) = S.lam s k * S.eps2 s k * (mom (u s) α - mom (u k) α)

/-- The scheme with `ε2 = ε4 = 0` on the edges with exactly one end on the wall (`isWall i ≠ isWall k`), and
unchanged elsewhere. -/
def cutWall {ι C Q : Type} {d : ℕ} (S : Data ι C Q d) (isWall : ι → Bool) : Data ι C Q d :=
  { S with
    eps2 := fun i k => if isWall i ≠ isWall k then 0 else S.eps2 i k
    eps4 := fun i k => if isWall i ≠ isWall k then 0 else S.eps4 i k }

/-- P4-15.4 (`prop:wallJST`(i), (ii)): setting `ε2 = ε4 = 0` on the wall-crossing edges, and only there, (i) removes
both terms on those edges; (ii) leaves the central flux, the closure, the viscous and the wall terms and the
dissipation of every other edge unchanged, so the residual changes exactly by the removed dissipation; the removed
second-difference terms produce `≤ 0` pair by pair (admissible states, `λ, ε2 ≥ 0`, Lemma `lem:eps2`), and `Π^(2)`
of the scheme is `Π^(2)` of the cut scheme plus these productions; `Π^(4)` of the scheme is `Π^(4)` of the cut scheme
plus the productions of the removed fourth-difference terms (evaluated in the model by P4-15.5); and the cut scheme satisfies the hypotheses of the
complete scheme whenever the original does, so P3-14.1-14.3 hold for it unchanged. -/
def P4_15_4 : Prop :=
  ∀ (ι C Q : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C] [Fintype Q] (d : ℕ)
    (S : Data ι C Q d) (bd : C × Fin (d + 1) → Bool) (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ)
    (u : ι → State d) (isWall : ι → Bool),
    let S' := cutWall S isWall
    (∀ i k, isWall i ≠ isWall k → diss2 S' u i k = 0 ∧ diss4 S' u i k = 0) ∧
    (∀ i k, isWall i = isWall k → diss2 S' u i k = diss2 S u i k ∧ diss4 S' u i k = diss4 S u i k) ∧
    (∀ i k, central S' u i k = central S u i k) ∧
    (∀ i, closure S' u i = closure S u i ∧ visc S' u i = visc S u i ∧ wall S' u i = wall S u i) ∧
    (∀ i, resid S' u i = resid S u i +
      ∑ k, if isWall i ≠ isWall k then diss2 S u i k - diss4 S u i k else 0) ∧
    ((∀ i, Admissible S.g (u i)) → (∀ i k, 0 ≤ S.lam i k ∧ 0 ≤ S.eps2 i k) →
      ∀ i k, pairF (w S u k - w S u i) (diss2 S u i k) ≤ 0) ∧
    Pi2 S u = Pi2 S' u +
      (1 / 2) * ∑ i, ∑ k, (if isWall i ≠ isWall k then pairF (w S u k - w S u i) (diss2 S u i k) else 0) ∧
    Pi4 S u = Pi4 S' u -
      (1 / 2) * ∑ i, ∑ k, (if isWall i ≠ isWall k then pairF (w S u k - w S u i) (diss4 S u i k) else 0) ∧
    (SchemeHyp S bd fq aq u → SchemeHyp S' bd fq aq u)

/-- P4-15.5 (`prop:wallJST`(iii)): a linear wall-normal profile on the geometric nodes `0, h, (1+r) h`:
`ũ_2 = ũ_s + (1+r)(ũ_k - ũ_s)`; the wall node has boundary-only neighbours at `y = 0`, so `L_s = 0` (normal part).
Then `L_k - L_s = (r-1)(ũ_k - ũ_s)` exactly, and the fourth-difference flux `-λ ε4 (L_s - L_k)` of `d_sk` produces
`[w]·(λ ε4 (L_k - L_s)) = ε4 (r-1) λ [w]·[ũ] ≥ 0` for admissible states, `r ≥ 1`, `λ, ε4 ≥ 0` (an anti-diffusion,
removed by the cut of P4-15.4). `[ũ] = H̄ [w]` with `H̄ = ∫_0^1 ∂ũ/∂w ds` along the straight path is the
fundamental theorem of calculus of P3-13.1. -/
def P4_15_5 : Prop :=
  ∀ (d : ℕ) (g : Gas) (us uk : State d) (r lam eps4 : ℝ),
    Admissible g us → Admissible g uk → 1 ≤ r → 0 ≤ lam → 0 ≤ eps4 →
    let ts := enthalpyState g us
    let tk := enthalpyState g uk
    let t2 := ts + (1 + r) • (tk - ts)
    let Ls : State d := 0
    let Lk := (ts - tk) + (t2 - tk)
    let dw := entropyVars g uk - entropyVars g us
    Lk - Ls = (r - 1) • (tk - ts) ∧
    pairF dw (-((lam * eps4) • (Ls - Lk))) = eps4 * (r - 1) * lam * pairF dw (tk - ts) ∧
    0 ≤ pairF dw (-((lam * eps4) • (Ls - Lk)))

/-- Linear model: `L_i = Σ_{k ∈ N*(i)} (u_k - u_i)`, `N*(i)` = the neighbours of `i` at an interior node, the wall
neighbours at a wall node. -/
def lapStar {V : Type} [Fintype V] (adj : V → V → Prop) [DecidableRel adj] (isWall : V → Bool) (u : V → ℂ)
    (i : V) : ℂ :=
  ∑ k, if adj i k ∧ (isWall i = true → isWall k = true) then u k - u i else 0

/-- Linear model of the fourth-difference operator with unit coefficients (`λ = ε4 = 1`, `ε2 = 0`) and the
wall-crossing edges cut: `R_i = Σ_{k ~ i, isWall k = isWall i} (L_k - L_i)` (`d_ik = -(L_i - L_k)`). -/
def fourthOp {V : Type} [Fintype V] (adj : V → V → Prop) [DecidableRel adj] (isWall : V → Bool) (u : V → ℂ)
    (i : V) : ℂ :=
  ∑ k, if adj i k ∧ isWall i = isWall k then lapStar adj isWall u k - lapStar adj isWall u i else 0

/-- P4-15.6 (`prop:wallJST`, last sentence): in the linear constant-coefficient model (symmetric graph, wall and
interior nodes, edges along the wall and interior edges keep the fourth difference, wall-crossing edges are cut), the
fourth-difference operator has a real, non-negative spectrum: every complex eigenvalue is real and `≥ 0`. -/
def P4_15_6 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj] (isWall : V → Bool),
    (∀ i k, adj i k → adj k i) →
    ∀ (μ : ℂ) (v : V → ℂ), v ≠ 0 → fourthOp adj isWall v = μ • v → μ.im = 0 ∧ 0 ≤ μ.re

end CFDLean.JST1.Spec
