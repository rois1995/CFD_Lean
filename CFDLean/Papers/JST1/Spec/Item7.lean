import CFDLean.Papers.JST1.Mixed.SplitMean
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Statements of item 7 (P2): `lem:dissgeom`(d) (lines 205-212, proof 930-936), stated exactly for quadratic
`q` (decision D2 = A), and the first part of `prop:consistency`(c) (288-289, proof 947-948). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- P2-7.1: for quadratic `q` and any coefficients, `½ Σ_k λ_k (q_k - q_i)` is the first-order part plus
`V K : ∇²q` with `K = (1/(4V)) Σ_k λ_k e_k ⊗ e_k`. -/
def P2_7_1 : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ℕ) (x : ι → Vec d) (i : ι) (lam : ι → ℝ) (V q0 : ℝ) (gq : Vec d)
    (H : Matrix (Fin d) (Fin d) ℝ), V ≠ 0 → H.IsSymm →
    let q : Vec d → ℝ := fun z => q0 + Num.dot gq z + (1 / 2) * Num.dot z (H.mulVec z)
    let K : Matrix (Fin d) (Fin d) ℝ := (1 / (4 * V)) • ∑ k, lam k • outer (x k - x i) (x k - x i)
    (1 / 2) * ∑ k, lam k * (q (x k) - q (x i)) =
      (1 / 2) * (∑ k, lam k * Num.dot (gq + H.mulVec (x i)) (x k - x i)) + V * frob K H

/-- P2-7.2: with `λ_k = σ_k |y_k|`: `|y| = |ν(y)| sec ϑ`, `sec ϑ ≥ 1`; `K(y) ⪰ K(ν)` in the Loewner order, with
equality iff `y_k ∥ e_k` on every pair with `σ_k > 0`. -/
def P2_7_2 : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ℕ) (e y : ι → Vec d) (σ : ι → ℝ) (V : ℝ),
    0 < V → (∀ k, 0 ≤ σ k) → (∀ k, 0 < Num.dot (y k) (e k)) →
    let K : (ι → Vec d) → Matrix (Fin d) (Fin d) ℝ :=
      fun z => (1 / (4 * V)) • ∑ k, (σ k * len (z k)) • outer (e k) (e k)
    let ν : ι → Vec d := fun k => WMesh.nuOf (y k) (e k)
    (∀ k, len (y k) = len (ν k) * (len (y k) * len (e k) / Num.dot (y k) (e k)) ∧
      1 ≤ len (y k) * len (e k) / Num.dot (y k) (e k)) ∧
    (K y - K ν).PosSemidef ∧
    (K y = K ν ↔ ∀ k, 0 < σ k → ∃ t : ℝ, 0 < t ∧ y k = t • e k)

/-- P2-7.3: `K_i = s G_i(y)/(4V_i)` if `σ_ik |e_ik| = s`; `tr K_i(ν) = d s/2` (at every vertex); and
`tr K_i(ν) ≤ (d/2) σ_max h_i`. -/
def P2_7_3 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d) (σ : ι → ι → ℝ)
    (s σmax h : ℝ) (y : ι → ι → Vec d) (i : ι), M.Valid → 0 < M.V i →
    let K : (ι → ι → Vec d) → Matrix (Fin d) (Fin d) ℝ :=
      fun z => (1 / (4 * M.V i)) • ∑ k, (σ i k * len (z i k)) • outer (M.e i k) (M.e i k)
    ((∀ k, k ≠ i → σ i k * len (M.e i k) = s) → K y = (s / (4 * M.V i)) • M.Gtensor y i) ∧
    ((∀ k, k ≠ i → σ i k * len (M.e i k) = s) → Matrix.trace (K M.nu) = d * s / 2) ∧
    ((∀ k, 0 ≤ σ i k ∧ σ i k ≤ σmax) → (∀ k, M.n i k ≠ 0 → len (M.e i k) ≤ h) →
      Matrix.trace (K M.nu) ≤ d / 2 * σmax * h)

/-- P2-7.4 (`prop:consistency`(c), first part): `Σ λ̂_ik |e_ik| ≤ d σ_max |Ω|` per pair (ordered pairs: `2d`). -/
def P2_7_4 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d) (vb : ι → ι → Vec d)
    (cb : ι → ι → ℝ) (σmax : ℝ), M.Valid →
    (∀ i k, 0 ≤ cb i k ∧ |Num.dot (vb i k) (WMesh.unit (M.e i k))| + cb i k ≤ σmax) →
    ∑ i, ∑ k, lamHat (vb i k) (cb i k) (M.e i k) (M.n i k) * len (M.e i k) ≤ 2 * d * σmax * M.volΩ

end CFDLean.JST1.Spec
