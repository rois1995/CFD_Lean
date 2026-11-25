import CFDLean.Geometry.MeshBoundary
import CFDLean.Papers.JST1.Euler.Boundary
import CFDLean.Entropy.PairFlux
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Statements of item 6 (P2): `prop:sbp` (lines 143-150, proof 882-890), `lem:bdefect` (300-308, proof
992-1020), `prop:consistency`(b) (284-287, proof 942-944), first sentence of `prop:defect` (163). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- P2-6.1 (`prop:sbp`): for any dual with `Σ_a W_a^T = |T|`: `c + cᵀ = B_c + 2s` with `s` symmetric, zero row sums
and entries `E_ik`; zero row sums of `c`, column sums `β`. -/
def P2_6_1 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d)
    (W : C → Fin (d + 1) → ℝ), (∀ T, ∑ a, W T a = M.vol T) →
    (∀ i k, M.cW W i k + M.cW W k i = M.B i k + (2 : ℝ) • M.EW W i k) ∧
    (∀ i k, M.EW W k i = M.EW W i k) ∧ (∀ i, ∑ k, M.EW W i k = 0) ∧
    (∀ i, ∑ k, M.cW W i k = 0) ∧ (∀ k, ∑ i, M.cW W i k = M.beta k)

/-- P2-6.2 (`prop:sbp` last sentence, `prop:defect` first sentence): on one nondegenerate simplex, with
`δ_a = W_a - m_T` (`Σ δ = 0`), all off-diagonal defect terms vanish iff `W = m_T`. -/
def P2_6_2 : Prop :=
  ∀ (d : ℕ) (T : Simplex d) (δ : Fin (d + 1) → ℝ), 1 ≤ d → T.Nondeg → ∑ a, δ a = 0 →
    ((∀ a b, a ≠ b → δ a • T.grad b + δ b • T.grad a = 0) ↔ ∀ a, δ a = 0)

/-- P2-6.3: on a conforming mesh, `β` and the boundary mass matrix `B_c = c + cᵀ` are sums over the boundary
facets; a vertex on no boundary facet is closed. -/
def P2_6_3 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d)
    (bd : C × Fin (d + 1) → Bool), M.Valid → 1 ≤ d → M.Conforming bd →
    (∀ i, M.beta i = ∑ p, if bd p ∧ i ∈ M.facetNodes p then (1 / (d : ℝ)) • M.areaVec p else 0) ∧
    (∀ i k, M.B i k = ∑ p, if bd p ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
        ((1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) • M.areaVec p else 0) ∧
    (∀ i, (∀ p, bd p = true → i ∉ M.facetNodes p) → M.Closed i)

/-- P2-6.4 (eq. pf-B2): for row sums 0, column sums `β`, any `B` with row sums `β`, `s^B = ½(c + cᵀ - B)`: the edge
form plus `½(B F + diag β F)` is `c F`. -/
def P2_6_4 : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (d : ℕ) (c B : ι → ι → Vec d) (β : ι → Vec d)
    (F : ι → Matrix κ (Fin d) ℝ),
    (∀ i, ∑ k, c i k = 0) → (∀ k, ∑ i, c i k = β k) → (∀ i, ∑ k, B i k = β i) →
    let n : ι → ι → Vec d := fun i k => c i k - c k i
    let s : ι → ι → Vec d := fun i k => (1 / 2 : ℝ) • (c i k + c k i - B i k)
    ∀ i, (∑ k, ((1 / 2 : ℝ) • (F i + F k)).mulVec (n i k)) + (∑ k, (F k - F i).mulVec (s i k)) +
        (1 / 2 : ℝ) • ((∑ k, (F k).mulVec (B i k)) + (F i).mulVec (β i)) = ∑ k, (F k).mulVec (c i k)

/-- P2-6.5 (`lem:bdefect`): `Fs p j` is the boundary flux through the area vector of boundary facet `p` at the state
of node `j`. The standard closure gives the lumped boundary term plus the defect `Π` per face (ordered pairs,
`A/(4d(d+1)) Σ_{i,j}` = `A/(2d(d+1)) Σ_{i<j}`). For linear nodal fluxes it is `½(B_c + diag β)F`, with weights
`(d+3) : 1`. -/
def P2_6_5 : Prop :=
  ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
    (bd : C × Fin (d + 1) → Bool) (w : ι → κ → ℝ) (ψ : ι → Vec d) (Fs : C × Fin (d + 1) → ι → κ → ℝ),
    M.Valid → 1 ≤ d → M.Conforming bd →
    let b : ι → κ → ℝ := fun i => ∑ p, if bd p ∧ i ∈ M.facetNodes p then
      ∑ j ∈ M.facetNodes p, stdWeight d i j • Fs p j else 0
    (∑ i, (Num.dot (ψ i) (M.beta i) - pairF (w i) (b i))) =
      ∑ p, if bd p then
        (1 / (d : ℝ)) * (∑ i ∈ M.facetNodes p, (Num.dot (ψ i) (M.areaVec p) - pairF (w i) (Fs p i))) +
        (1 / (4 * (d : ℝ) * (d + 1))) *
          ∑ i ∈ M.facetNodes p, ∑ j ∈ M.facetNodes p, pairF (w j - w i) (Fs p j - Fs p i)
      else 0

/-- P2-6.5b: for linear fluxes the standard closure is `½(B_c + diag β) F`; weights `(d+3) : 1`. -/
def P2_6_5b : Prop :=
  ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
    (bd : C × Fin (d + 1) → Bool) (F : ι → Matrix κ (Fin d) ℝ), M.Valid → 1 ≤ d → M.Conforming bd →
    (∀ i, (∑ k, (F k).mulVec ((1 / 2 : ℝ) • (M.B i k + if i = k then M.beta i else 0))) =
      ∑ p, if bd p ∧ i ∈ M.facetNodes p then
        ∑ j ∈ M.facetNodes p, stdWeight d i j • (F j).mulVec (M.areaVec p) else 0) ∧
    (∀ i j : ι, i ≠ j → stdWeight d i i = ((d : ℝ) + 3) * stdWeight d i j)

/-- P2-6.6 (`lem:bdefect`, slip wall): with the pressure flux the defect `[w]·[F*]` takes both signs on admissible
states (the lumped term vanishes: P2-8.5). -/
def P2_6_6 : Prop :=
  ∀ (d : ℕ) (g : Gas) (y : Vec d), 1 ≤ d → y ≠ 0 →
    (∃ U1 U2 : State d, Admissible g U1 ∧ Admissible g U2 ∧
      0 < pairF (entropyVars g U2 - entropyVars g U1) (pressFlux g U2 y - pressFlux g U1 y)) ∧
    (∃ U1 U2 : State d, Admissible g U1 ∧ Admissible g U2 ∧
      pairF (entropyVars g U2 - entropyVars g U1) (pressFlux g U2 y - pressFlux g U1 y) < 0)

/-- P2-6.7 (`prop:consistency`(b)): at a closed vertex the mean flux on `n_ik` is the Galerkin form
`Σ_{T∋i} m_T Σ_k g_k^T · F_k = Σ_k c_ik · F_k`. -/
def P2_6_7 : Prop :=
  ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
    (F : ι → Matrix κ (Fin d) ℝ) (i : ι), M.Valid → M.Closed i →
    (∑ k, ((1 / 2 : ℝ) • (F i + F k)).mulVec (M.n i k)) = ∑ k, (F k).mulVec (M.c i k) ∧
    (∑ k, (F k).mulVec (M.c i k)) = ∑ T, ∑ a, if M.vert T a = i then
      (M.ω T * M.m T) • ∑ b, (F (M.vert T b)).mulVec (M.g T b) else 0

end CFDLean.JST1.Spec
