import CFDLean.Geometry.MeshBoundary
import CFDLean.Papers.JST1.Euler.IsmailRoe
import CFDLean.Papers.JST1.Euler.Boundary
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Statements of item 8 (P2): `thm:closure` (lines 309-321, proof 1022-1043). Quadrature points `q` carry the
values `φ q k` of the P1 basis, the scaled normals `N q = a_q N_f`, the projected states `ũ_q` and the boundary
fluxes `F*_q`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- P2-8.0 (entropy projection, Euler): every `w` with `w_E < 0` is `w(u)` of exactly one admissible `u`. -/
def P2_8_0 : Prop :=
  ∀ (d : ℕ) (g : Gas) (W : State d), W .energy < 0 → ∃! U : State d, Admissible g U ∧ entropyVars g U = W

/-- P2-8.1: exact boundary entropy identity, and conservation `Σ_i b_i = Σ_q F*_q`. -/
def P2_8_1 : Prop :=
  ∀ (ι Q S κ : Type) [Fintype ι] [Fintype Q] [Fintype κ] (d : ℕ) (w : S → κ → ℝ) (ψ : S → Vec d)
    (Fec : S → S → Vec d → κ → ℝ) (u : ι → S) (φ : Q → ι → ℝ) (N : Q → Vec d) (ut : Q → S) (Fs : Q → κ → ℝ),
    (∀ a b y, Fec a b y = Fec b a y) →
    (∀ a b y, pairF (w b - w a) (Fec a b y) = Num.dot (ψ b - ψ a) y) →
    (∀ q, ∑ k, φ q k = 1) → (∀ q, w (ut q) = ∑ k, φ q k • w (u k)) →
    let beta : ι → Vec d := fun i => ∑ q, φ q i • N q
    let b : ι → κ → ℝ := fun i => ∑ q, φ q i •
      (Fec (u i) (ut q) (N q) - ∑ k, φ q k • Fec (ut q) (u k) (N q) + Fs q)
    (∑ i, (Num.dot (ψ (u i)) (beta i) - pairF (w (u i)) (b i))) =
      ∑ q, (Num.dot (ψ (ut q)) (N q) - pairF (w (ut q)) (Fs q)) ∧
    ∑ i, b i = ∑ q, Fs q

/-- P2-8.2 (free stream): a uniform state with `F*_q = F(u)·N_q` and `Σ_q φ_qi N_q = -Σ_k n_ik` has zero residual
(the closure's free-stream property assumed in P1-2.7 is proved here). -/
def P2_8_2 : Prop :=
  ∀ (ι Q S κ : Type) [Fintype ι] [Fintype Q] [Fintype κ] (d : ℕ) (Fec : S → S → Vec d → κ → ℝ)
    (phys : S → Vec d → κ → ℝ) (U : S) (φ : Q → ι → ℝ) (N : Q → Vec d) (n : ι → ι → Vec d),
    (∀ a b, IsLinearMap ℝ (Fec a b)) → (∀ y, Fec U U y = phys U y) → (∀ q, ∑ k, φ q k = 1) →
    (∀ i, ∑ q, φ q i • N q = -∑ k, n i k) →
    let b : ι → κ → ℝ := fun i => ∑ q, φ q i •
      (Fec U U (N q) - ∑ k, φ q k • Fec U U (N q) + phys U (N q))
    ∀ i, -(∑ k, Fec U U (n i k)) - b i = 0

/-- P2-8.3 (linear fluxes): with `F^ec = ½(F_a + F_b)·y`, `F(ũ_q) = Σ_k φ_qk F_k` and `F*_q = F(ũ_q)·N_q`:
`b_i = ½(F_i·β_i + Σ_k F_k·Σ_q φ_qi φ_qk N_q)`. -/
def P2_8_3 : Prop :=
  ∀ (ι Q S κ : Type) [Fintype ι] [Fintype Q] [Fintype κ] (d : ℕ) (Fec : S → S → Vec d → κ → ℝ)
    (Fl : S → Matrix κ (Fin d) ℝ) (u : ι → S) (φ : Q → ι → ℝ) (N : Q → Vec d) (ut : Q → S),
    (∀ a b y, Fec a b y = ((1 / 2 : ℝ) • (Fl a + Fl b)).mulVec y) →
    (∀ q, Fl (ut q) = ∑ k, φ q k • Fl (u k)) → (∀ q, ∑ k, φ q k = 1) →
    let beta : ι → Vec d := fun i => ∑ q, φ q i • N q
    let b : ι → κ → ℝ := fun i => ∑ q, φ q i •
      (Fec (u i) (ut q) (N q) - ∑ k, φ q k • Fec (ut q) (u k) (N q) + (Fl (ut q)).mulVec (N q))
    ∀ i, b i = (1 / 2 : ℝ) • ((Fl (u i)).mulVec (beta i) +
      ∑ k, (Fl (u k)).mulVec (∑ q, (φ q i * φ q k) • N q))

/-- P2-8.4: a face rule with (H1), (H2) on every boundary facet of a conforming mesh gives
`Σ_q φ_qi N_q = β_i` and `Σ_q φ_qi φ_qk N_q = B_c ik`; so P2-8.3 is the closure of `lem:bdefect`. -/
def P2_8_4 : Prop :=
  ∀ (ι C Q : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C] [Fintype Q] (d : ℕ) (M : WMesh ι C d)
    (bd : C × Fin (d + 1) → Bool) (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ) (φ : Q → ι → ℝ),
    M.Valid → 1 ≤ d → M.Conforming bd → (∀ q, bd (fq q) = true) →
    (∀ q k, k ∉ M.facetNodes (fq q) → φ q k = 0) →
    (∀ p, bd p = true → ∀ i ∈ M.facetNodes p,
      (∑ q, if fq q = p then aq q * φ q i else 0) = 1 / (d : ℝ)) →
    (∀ p, bd p = true → ∀ i ∈ M.facetNodes p, ∀ k ∈ M.facetNodes p,
      (∑ q, if fq q = p then aq q * φ q i * φ q k else 0) = (1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) →
    let N : Q → Vec d := fun q => aq q • M.areaVec (fq q)
    (∀ i, ∑ q, φ q i • N q = M.beta i) ∧ (∀ i k, ∑ q, (φ q i * φ q k) • N q = M.B i k)

/-- P2-8.5 (slip wall): with the pressure flux, the point term `ψ̃·N - w̃·F*` is zero for any admissible state. -/
def P2_8_5 : Prop :=
  ∀ (d : ℕ) (g : Gas) (U : State d) (y : Vec d), Admissible g U →
    Num.dot (fluxPot U) y - pairF (entropyVars g U) (pressFlux g U y) = 0

/-- P2-8.6 (far field): an entropy-stable `F*` against the ghost state bounds the point term by the ghost's
numerical entropy flux; the Ismail-Roe flux with Rusanov-type dissipation `λ ≥ 0` is such an `F*`. -/
def P2_8_6 : Prop :=
  (∀ (S κ : Type) [Fintype κ] (d : ℕ) (w : S → κ → ℝ) (ψ : S → Vec d) (ut ug : S) (N : Vec d) (Fs : κ → ℝ),
    pairF (w ug - w ut) Fs ≤ Num.dot (ψ ug - ψ ut) N →
    Num.dot (ψ ut) N - pairF (w ut) Fs ≤ Num.dot (ψ ug) N - pairF (w ug) Fs) ∧
  (∀ (d : ℕ) (g : Gas) (Ut Ug : State d) (N : Vec d) (lam : ℝ), Admissible g Ut → Admissible g Ug → 0 ≤ lam →
    pairF (entropyVars g Ug - entropyVars g Ut) (ismailRoe g Ut Ug N - (lam / 2) • (Ug - Ut)) ≤
      Num.dot (fluxPot Ug - fluxPot Ut) N)

end CFDLean.JST1.Spec
