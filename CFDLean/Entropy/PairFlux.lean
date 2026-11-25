import CFDLean.Geometry.MeshBoundary
set_option cleanup.letToHave false -- MC-N: keep the `let` binders of the moved JST definitions and statements
set_option linter.unusedSectionVars false

/-! Antisymmetric pair fluxes and entropy-conservative two-point fluxes (P1-2.1, P1-2.2, P1-2.6, P1-2.7), the edge
form with a boundary split (P2-6.4, eq. pf-B2), the standard boundary closure (P2-6.5, P2-6.5b) and the quadrature
boundary closure (P2-8.1 to P2-8.4).

MC-N: `stdWeight` moved verbatim from JST_Paper_Lean `Paper1/Spec/Item6.lean`; proofs from
`Paper1/Proofs/{Item2Generic,Item6,Item8}.lean`. -/
noncomputable section
open scoped BigOperators
namespace CFDLean.Num

/-- Face weights of the standard closure: `ω_ij = δ_ij/d + ½(μ_ij - δ_ij/d)`, `μ_ij = (1+δ_ij)/(d(d+1))`. -/
def stdWeight {ι : Type} [DecidableEq ι] (d : ℕ) (i j : ι) : ℝ :=
  (1 / 2) * ((1 + if i = j then 1 else 0) / ((d : ℝ) * (d + 1)) + (if i = j then 1 else 0) / d)

end CFDLean.Num

namespace CFDLean.Num.Internal

section

theorem pairF_sum {κ ι : Type} [Fintype κ] (x : κ → ℝ) (s : Finset ι) (F : ι → κ → ℝ) :
    pairF x (∑ k ∈ s, F k) = ∑ k ∈ s, pairF x (F k) := by
  simp only [pairF, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem pairF_sub_left {κ : Type} [Fintype κ] (x y z : κ → ℝ) :
    pairF (x - y) z = pairF x z - pairF y z := by
  simp only [pairF, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem pairF_neg_right {κ : Type} [Fintype κ] (x z : κ → ℝ) : pairF x (-z) = -pairF x z := by
  simp only [pairF, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem antisym_sum_zero {ι κ : Type} [Fintype ι] (F : ι → ι → κ → ℝ) (hF : ∀ i k, F k i = -F i k) :
    (∑ i, ∑ k, F i k) = 0 := by
  have h1 : (∑ i, ∑ k, F i k) = ∑ i, ∑ k, F k i := Finset.sum_comm
  have h2 : (∑ i, ∑ k, F k i) = -∑ i, ∑ k, F i k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hF i k
  funext c
  have := congrFun (h1.trans h2) c
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  linarith

theorem antisym_production {ι κ : Type} [Fintype ι] [Fintype κ] (F : ι → ι → κ → ℝ) (w : ι → κ → ℝ)
    (hF : ∀ i k, F k i = -F i k) :
    -(∑ i, pairF (w i) (∑ k, F i k)) = (1 / 2) * ∑ i, ∑ k, pairF (w k - w i) (F i k) := by
  have hA : (∑ i, ∑ k, pairF (w k) (F i k)) = -∑ i, ∑ k, pairF (w i) (F i k) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hF k i, pairF_neg_right]
  simp only [pairF_sum, pairF_sub_left, Finset.sum_sub_distrib, hA]
  ring

/-- MC-N.P1-2.1 (JST `Paper1.Spec.P1_2_1`, proof `Paper1.Proofs.p1_2_1`). P1-2.1: antisymmetric pair fluxes: conservation and production. -/
theorem _root_.CFDLean.Num.antisymmetric_pairFlux :
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (F : ι → ι → κ → ℝ) (w : ι → κ → ℝ),
      (∀ i k, F k i = -F i k) →
      (∑ i, ∑ k, F i k) = 0 ∧
      -(∑ i, pairF (w i) (∑ k, F i k)) = (1 / 2) * ∑ i, ∑ k, pairF (w k - w i) (F i k) := by
  intro ι κ _ _ F w hF
  exact ⟨antisym_sum_zero F hF, antisym_production F w hF⟩

theorem dot_sum_right {d : ℕ} {ι : Type} (x : Vec d) (s : Finset ι) (y : ι → Vec d) :
    dot x (∑ k ∈ s, y k) = ∑ k ∈ s, dot x (y k) := by
  simp only [dot, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- MC-N.P1-2.2 (JST `Paper1.Spec.P1_2_2`, proof `Paper1.Proofs.p1_2_2`). P1-2.2 (`lem:ec`): an entropy-conservative central part produces only `Σ_i ψ_i·β_i`. -/
theorem _root_.CFDLean.Num.entropyConservative_production :
    ∀ (ι S κ : Type) [Fintype ι] [Fintype κ] (d : ℕ) (w : S → κ → ℝ) (ψ : S → Vec d)
      (Fec : S → S → Vec d → κ → ℝ) (n : ι → ι → Vec d) (u : ι → S),
      (∀ i k, n k i = -n i k) →
      (∀ a b y, Fec a b y = Fec b a y) →
      (∀ a b, IsLinearMap ℝ (Fec a b)) →
      (∀ a b y, pairF (w b - w a) (Fec a b y) = dot (ψ b - ψ a) y) →
      let beta : ι → Vec d := fun i => -∑ k, n i k
      let Rc : ι → κ → ℝ := fun i => ∑ k, Fec (u i) (u k) (n i k)
      (-(∑ i, pairF (w (u i)) (Rc i))) = (1 / 2) * ∑ i, ∑ k, dot (ψ (u k) - ψ (u i)) (n i k) ∧
      (1 / 2) * ∑ i, ∑ k, dot (ψ (u k) - ψ (u i)) (n i k) = ∑ i, dot (ψ (u i)) (beta i) := by
  intro ι S κ _ _ d w ψ Fec n u hn hsym hlin htad beta Rc
  -- the central pair flux is antisymmetric
  have hF : ∀ i k, Fec (u k) (u i) (n k i) = -Fec (u i) (u k) (n i k) := by
    intro i k
    rw [hsym, hn, (hlin _ _).map_neg]
  have hprod := antisym_production (fun i k => Fec (u i) (u k) (n i k)) (fun i => w (u i)) hF
  refine ⟨?_, ?_⟩
  · rw [hprod]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    exact htad _ _ _
  · -- (1/2) ΣΣ (ψk - ψi)·n_ik = Σ ψ_i·β_i
    have hdot_sub : ∀ (a b y : Vec d), dot (a - b) y = dot a y - dot b y := by
      intro a b y; simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    have hdot_neg : ∀ (a y : Vec d), dot a (-y) = -dot a y := by
      intro a y; simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    have hB : (∑ i, ∑ k, dot (ψ (u k)) (n i k)) = -∑ i, ∑ k, dot (ψ (u i)) (n i k) := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hn k i, hdot_neg]
    simp only [beta, hdot_neg, dot_sum_right, hdot_sub, Finset.sum_sub_distrib, hB, Finset.sum_neg_distrib]
    ring

/-- MC-N.P1-2.6 (JST `Paper1.Spec.P1_2_6`, proof `Paper1.Proofs.p1_2_6`). P1-2.6 (conservation): central flux plus scalar dissipation with symmetric coefficients. -/
theorem _root_.CFDLean.Num.dissipativePairFlux_conservation :
    ∀ (ι S κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] (d : ℕ) (Fec : S → S → Vec d → κ → ℝ)
      (n : ι → ι → Vec d) (u : ι → S) (ut : ι → κ → ℝ) (lam eps2 eps4 : ι → ι → ℝ)
      (Nstar : ι → Finset ι) (b : ι → κ → ℝ),
      (∀ i k, n k i = -n i k) → (∀ a b y, Fec a b y = Fec b a y) → (∀ a b, IsLinearMap ℝ (Fec a b)) →
      (∀ i k, lam k i = lam i k) → (∀ i k, eps2 k i = eps2 i k) → (∀ i k, eps4 k i = eps4 i k) →
      let L : ι → κ → ℝ := fun i => ∑ k ∈ Nstar i, (ut k - ut i)
      let F : ι → ι → κ → ℝ := fun i k =>
        Fec (u i) (u k) (n i k) + lam i k • (eps2 i k • (ut i - ut k) - eps4 i k • (L i - L k))
      (∀ i k, F k i = -F i k) ∧ ∑ i, (-(∑ k, F i k) - b i) = -∑ i, b i := by
  intro ι S κ _ _ _ d Fec n u ut lam eps2 eps4 Nstar b hn hsym hlin hlam he2 he4 L F
  have hF : ∀ i k, F k i = -F i k := by
    intro i k
    simp only [F]
    rw [hsym, hn, (hlin _ _).map_neg, hlam, he2, he4]
    funext c
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  refine ⟨hF, ?_⟩
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, antisym_sum_zero F hF, neg_zero, zero_sub]

/-- MC-N.P1-2.7 (JST `Paper1.Spec.P1_2_7`, proof `Paper1.Proofs.p1_2_7`). P1-2.7 (free stream): a uniform state with the matching boundary data has zero residual. -/
theorem _root_.CFDLean.Num.dissipativePairFlux_freeStream :
    ∀ (ι S κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] (d : ℕ) (Fec : S → S → Vec d → κ → ℝ)
      (phys : S → Vec d → κ → ℝ) (n : ι → ι → Vec d) (U : S) (ut0 : κ → ℝ) (lam eps2 eps4 : ι → ι → ℝ)
      (Nstar : ι → Finset ι),
      (∀ a b, IsLinearMap ℝ (Fec a b)) → (∀ y, Fec U U y = phys U y) →
      let beta : ι → Vec d := fun i => -∑ k, n i k
      let L : ι → κ → ℝ := fun i => ∑ _k ∈ Nstar i, (ut0 - ut0)
      let F : ι → ι → κ → ℝ := fun i k =>
        Fec U U (n i k) + lam i k • (eps2 i k • (ut0 - ut0) - eps4 i k • (L i - L k))
      ∀ i, -(∑ k, F i k) - phys U (beta i) = 0 := by
  intro ι S κ _ _ _ d Fec phys n U ut0 lam eps2 eps4 Nstar hlin hcons beta L F i
  have hlinP : IsLinearMap ℝ (phys U) := by
    have : phys U = Fec U U := funext fun y => (hcons y).symm
    rw [this]; exact hlin U U
  let φ : Vec d →ₗ[ℝ] (κ → ℝ) := hlinP.mk' _
  have hFi : ∀ k, F i k = phys U (n i k) := by
    intro k
    simp only [F, L, hcons, sub_self, Finset.sum_const_zero, smul_zero, add_zero]
  have hsum : (∑ k, F i k) = phys U (∑ k, n i k) := by
    simp only [hFi]
    exact (map_sum φ (fun k => n i k) Finset.univ).symm
  have hneg : phys U (beta i) = -phys U (∑ k, n i k) := by
    simp only [beta]
    exact φ.map_neg _
  rw [hsum, hneg]
  abel

end

namespace Sbp6

theorem pairF_sub_l {κ : Type} [Fintype κ] (x y z : κ → ℝ) : pairF (x - y) z = pairF x z - pairF y z := by
  simp only [pairF, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem pairF_sub_r {κ : Type} [Fintype κ] (x y z : κ → ℝ) : pairF x (y - z) = pairF x y - pairF x z := by
  simp only [pairF, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pairF_ite {κ : Type} [Fintype κ] (x : κ → ℝ) (P : Prop) [Decidable P] (z : κ → ℝ) :
    pairF x (if P then z else 0) = if P then pairF x z else 0 := by
  split_ifs <;> simp [pairF]

theorem sum_bd_mem {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid X] (b : Bool) (s : Finset ι) (g : ι → X) :
    ∑ i, (if b = true ∧ i ∈ s then g i else 0) = if b = true then ∑ i ∈ s, g i else 0 := by
  cases b
  · simp
  · simp only [true_and, ite_true]
    rw [← Finset.sum_filter]
    congr 1
    ext i; simp

/-- Face identity of the standard closure on a face with `d` nodes. -/
theorem face_identity {ι κ : Type} [DecidableEq ι] [Fintype κ] (d : ℕ) (hd : 1 ≤ d) (s : Finset ι)
    (hs : s.card = d) (w F : ι → κ → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, stdWeight d i j * pairF (w i) (F j) =
      (1 / (d : ℝ)) * (∑ i ∈ s, pairF (w i) (F i)) -
        (1 / (4 * (d : ℝ) * (d + 1))) * ∑ i ∈ s, ∑ j ∈ s, pairF (w j - w i) (F j - F i) := by
  set S := ∑ i ∈ s, ∑ j ∈ s, pairF (w i) (F j) with hS
  set D := ∑ i ∈ s, pairF (w i) (F i) with hD
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : ∑ i ∈ s, ∑ j ∈ s, stdWeight d i j * pairF (w i) (F j) =
      (1 / 2) * (1 / ((d : ℝ) * (d + 1))) * S + (1 / 2) * (1 / ((d : ℝ) * (d + 1)) + 1 / d) * D := by
    have e : ∀ i ∈ s, ∑ j ∈ s, stdWeight d i j * pairF (w i) (F j) =
        (1 / 2) * (1 / ((d : ℝ) * (d + 1))) * (∑ j ∈ s, pairF (w i) (F j)) +
          (1 / 2) * (1 / ((d : ℝ) * (d + 1)) + 1 / d) * pairF (w i) (F i) := by
      intro i hi
      have : ∀ j, stdWeight d i j * pairF (w i) (F j) =
          (1 / 2) * (1 / ((d : ℝ) * (d + 1))) * pairF (w i) (F j) +
            (if i = j then (1 / 2) * (1 / ((d : ℝ) * (d + 1)) + 1 / d) * pairF (w i) (F j) else 0) := by
        intro j
        unfold stdWeight
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_ite_eq, ite_eq_left hi]
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h2 : ∑ i ∈ s, ∑ j ∈ s, pairF (w j - w i) (F j - F i) = 2 * d * D - 2 * S := by
    have e : ∀ i j, pairF (w j - w i) (F j - F i) =
        pairF (w j) (F j) - pairF (w j) (F i) - pairF (w i) (F j) + pairF (w i) (F i) := by
      intro i j
      rw [pairF_sub_l, pairF_sub_r, pairF_sub_r]; ring
    have hsc : ∑ i ∈ s, ∑ j ∈ s, pairF (w j) (F i) = S := Finset.sum_comm
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, hs, nsmul_eq_mul, hsc,
      ← Finset.mul_sum, ← hS, ← hD]
    ring
  rw [h1, h2]
  field_simp
  ring

theorem dot_sum_r {d : ℕ} {β : Type} (s : Finset β) (u : Vec d) (f : β → Vec d) :
    dot u (∑ x ∈ s, f x) = ∑ x ∈ s, dot u (f x) := by
  simp only [dot, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem dot_smul_r' {d : ℕ} (c : ℝ) (u v : Vec d) : dot u (c • v) = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_ite_r {d : ℕ} (u : Vec d) (P : Prop) [Decidable P] (v : Vec d) :
    dot u (if P then v else 0) = if P then dot u v else 0 := by
  split_ifs <;> simp [dot]

theorem mulVec_ite {κ : Type} [Fintype κ] {d : ℕ} (A : Matrix κ (Fin d) ℝ) (P : Prop) [Decidable P] (v : Vec d) :
    A.mulVec (if P then v else 0) = if P then A.mulVec v else 0 := by
  split_ifs <;> simp

end Sbp6

section
open Sbp6

/-- MC-N.P2-6.4 (JST `Paper1.Spec.P2_6_4`, proof `Paper1.Proofs.p2_6_4`). P2-6.4 (eq. pf-B2): for row sums 0, column sums `β`, any `B` with row sums `β`, `s^B = ½(c + cᵀ - B)`: the edge form plus `½(B F + diag β F)` is `c F`. -/
theorem _root_.CFDLean.Num.edgeForm_boundary_split :
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (d : ℕ) (c B : ι → ι → Vec d) (β : ι → Vec d)
      (F : ι → Matrix κ (Fin d) ℝ),
      (∀ i, ∑ k, c i k = 0) → (∀ k, ∑ i, c i k = β k) → (∀ i, ∑ k, B i k = β i) →
      let n : ι → ι → Vec d := fun i k => c i k - c k i
      let s : ι → ι → Vec d := fun i k => (1 / 2 : ℝ) • (c i k + c k i - B i k)
      ∀ i, (∑ k, ((1 / 2 : ℝ) • (F i + F k)).mulVec (n i k)) + (∑ k, (F k - F i).mulVec (s i k)) +
          (1 / 2 : ℝ) • ((∑ k, (F k).mulVec (B i k)) + (F i).mulVec (β i)) = ∑ k, (F k).mulVec (c i k) := by
  intro ι κ _ _ d c B β F h1 h2 h3 n s i
  have per : ∀ k, ((1 / 2 : ℝ) • (F i + F k)).mulVec (c i k - c k i) +
      (F k - F i).mulVec ((1 / 2 : ℝ) • (c i k + c k i - B i k)) =
      (F k).mulVec (c i k) - (F i).mulVec (c k i) + (1 / 2 : ℝ) • (F i).mulVec (B i k) -
        (1 / 2 : ℝ) • (F k).mulVec (B i k) := by
    intro k
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_sub, Matrix.mulVec_smul]
    ext r
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcol : ∑ k, c k i = β i := h2 i
  rw [← Finset.sum_add_distrib]
  simp only [n, s]
  rw [Finset.sum_congr rfl fun k _ => per k]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum]
  rw [mulVec_fsum (F i) (fun k => c k i), mulVec_fsum (F i) (fun k => B i k), hcol, h3]
  ext r
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- MC-N.P2-6.5 (JST `Paper1.Spec.P2_6_5`, proof `Paper1.Proofs.p2_6_5`). P2-6.5 (`lem:bdefect`): `Fs p j` is the boundary flux through the area vector of boundary facet `p` at the state of node `j`. The standard closure gives the lumped boundary term plus the defect `Π` per face (ordered pairs, `A/(4d(d+1)) Σ_{i,j}` = `A/(2d(d+1)) Σ_{i<j}`). For linear nodal fluxes it is `½(B_c + diag β)F`, with weights `(d+3) : 1`. -/
theorem _root_.CFDLean.Num.WMesh.standardClosure_entropy :
    ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
      (bd : C × Fin (d + 1) → Bool) (w : ι → κ → ℝ) (ψ : ι → Vec d) (Fs : C × Fin (d + 1) → ι → κ → ℝ),
      M.Valid → 1 ≤ d → M.Conforming bd →
      let b : ι → κ → ℝ := fun i => ∑ p, if bd p ∧ i ∈ M.facetNodes p then
        ∑ j ∈ M.facetNodes p, stdWeight d i j • Fs p j else 0
      (∑ i, (dot (ψ i) (M.beta i) - pairF (w i) (b i))) =
        ∑ p, if bd p then
          (1 / (d : ℝ)) * (∑ i ∈ M.facetNodes p, (dot (ψ i) (M.areaVec p) - pairF (w i) (Fs p i))) +
          (1 / (4 * (d : ℝ) * (d + 1))) *
            ∑ i ∈ M.facetNodes p, ∑ j ∈ M.facetNodes p, pairF (w j - w i) (Fs p j - Fs p i)
        else 0 := by
  intro ι C κ _ _ _ _ d M bd w ψ Fs _hM hd hC
  dsimp only
  have hβ : ∑ i, dot (ψ i) (M.beta i) = ∑ p, if bd p = true then
      (1 / (d : ℝ)) * ∑ i ∈ M.facetNodes p, dot (ψ i) (M.areaVec p) else 0 := by
    simp only [beta_bd M bd hC hd, dot_sum_r, dot_ite_r, dot_smul_r']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [sum_bd_mem, Finset.mul_sum]
  have hw : ∑ i, pairF (w i) (∑ p, if bd p = true ∧ i ∈ M.facetNodes p then
      ∑ j ∈ M.facetNodes p, stdWeight d i j • Fs p j else 0) =
      ∑ p, if bd p = true then ∑ i ∈ M.facetNodes p, ∑ j ∈ M.facetNodes p,
        stdWeight d i j * pairF (w i) (Fs p j) else 0 := by
    simp only [pairF_sum', pairF_ite, pairF_smul']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [sum_bd_mem]
  rw [Finset.sum_sub_distrib, hβ, hw, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs
  · rw [face_identity d hd _ (card_facetNodes M p) w (Fs p), Finset.sum_sub_distrib]
    ring
  · simp

/-- MC-N.P2-6.5b (JST `Paper1.Spec.P2_6_5b`, proof `Paper1.Proofs.p2_6_5b`). P2-6.5b: for linear fluxes the standard closure is `½(B_c + diag β) F`; weights `(d+3) : 1`. -/
theorem _root_.CFDLean.Num.WMesh.standardClosure_linear :
    ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
      (bd : C × Fin (d + 1) → Bool) (F : ι → Matrix κ (Fin d) ℝ), M.Valid → 1 ≤ d → M.Conforming bd →
      (∀ i, (∑ k, (F k).mulVec ((1 / 2 : ℝ) • (M.B i k + if i = k then M.beta i else 0))) =
        ∑ p, if bd p ∧ i ∈ M.facetNodes p then
          ∑ j ∈ M.facetNodes p, stdWeight d i j • (F j).mulVec (M.areaVec p) else 0) ∧
      (∀ i j : ι, i ≠ j → stdWeight d i i = ((d : ℝ) + 3) * stdWeight d i j) := by
  intro ι C κ _ _ _ _ d M bd F _hM hd hC
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨?_, ?_⟩
  · intro i
    set coef : ι → ι → ℝ := fun i k => (1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1)) with hcoef
    have hB : ∑ k, (F k).mulVec (M.B i k) = ∑ p, if bd p = true ∧ i ∈ M.facetNodes p then
        ∑ k ∈ M.facetNodes p, coef i k • (F k).mulVec (M.areaVec p) else 0 := by
      simp only [B_bd M bd hC hd, ← mulVec_fsum, mulVec_ite, Matrix.mulVec_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : bd p = true ∧ i ∈ M.facetNodes p
      · rw [ite_eq_left hp, ← Finset.sum_filter]
        refine Finset.sum_congr (by ext k; simp [hp.1, hp.2]) fun k _ => rfl
      · rw [ite_eq_right hp]
        refine Finset.sum_eq_zero fun k _ => ite_eq_right fun h => hp ⟨h.1, h.2.1⟩
    have hb : (F i).mulVec (M.beta i) = ∑ p, if bd p = true ∧ i ∈ M.facetNodes p then
        (1 / (d : ℝ)) • (F i).mulVec (M.areaVec p) else 0 := by
      simp only [beta_bd M bd hC hd, ← mulVec_fsum, mulVec_ite, Matrix.mulVec_smul]
    have hL : ∑ k, (F k).mulVec ((1 / 2 : ℝ) • (M.B i k + if i = k then M.beta i else 0)) =
        (1 / 2 : ℝ) • (∑ k, (F k).mulVec (M.B i k) + (F i).mulVec (M.beta i)) := by
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, mulVec_ite, Finset.sum_add_distrib,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.smul_sum, smul_add]
    rw [hL, hB, hb, ← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : bd p = true ∧ i ∈ M.facetNodes p
    · rw [ite_eq_left hp, ite_eq_left hp, ite_eq_left hp]
      have e : ∀ j, stdWeight d i j • (F j).mulVec (M.areaVec p) =
          (1 / 2 : ℝ) • (coef i j • (F j).mulVec (M.areaVec p)) +
            (if i = j then (1 / 2 : ℝ) • ((1 / (d : ℝ)) • (F i).mulVec (M.areaVec p)) else 0) := by
        intro j
        unfold stdWeight
        by_cases hij : i = j
        · subst hij; simp only [ite_true, hcoef, smul_smul, ← add_smul]; congr 1; ring
        · simp only [hij, ite_false, hcoef, smul_smul, add_zero]
          congr 1; ring
      rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left hp.2,
        ← Finset.smul_sum, smul_add]
    · rw [ite_eq_right hp, ite_eq_right hp, ite_eq_right hp, add_zero, smul_zero]
  · intro i j hij
    unfold stdWeight
    rw [ite_eq_left rfl, ite_eq_right hij]
    field_simp
    ring

end

namespace Cl8

section
variable {κ : Type} [Fintype κ]

theorem pr_sum {Q : Type} (s : Finset Q) (x : κ → ℝ) (f : Q → κ → ℝ) :
    pairF x (∑ q ∈ s, f q) = ∑ q ∈ s, pairF x (f q) := by
  unfold pairF
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem pl_sum {Q : Type} (s : Finset Q) (f : Q → κ → ℝ) (y : κ → ℝ) :
    pairF (∑ q ∈ s, f q) y = ∑ q ∈ s, pairF (f q) y := by
  unfold pairF
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem pr_smul (x y : κ → ℝ) (c : ℝ) : pairF x (c • y) = c * pairF x y := by
  simp only [pairF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem pl_smul (x y : κ → ℝ) (c : ℝ) : pairF (c • x) y = c * pairF x y := by
  simp only [pairF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem pr_add (x y z : κ → ℝ) : pairF x (y + z) = pairF x y + pairF x z := by
  simp only [pairF, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pr_sub (x y z : κ → ℝ) : pairF x (y - z) = pairF x y - pairF x z := by
  simp only [pairF, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pl_sub (x y z : κ → ℝ) : pairF (x - y) z = pairF x z - pairF y z := by
  simp only [pairF, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

end

section
variable {d : ℕ}

theorem dr_sum {Q : Type} (s : Finset Q) (x : Vec d) (f : Q → Vec d) :
    dot x (∑ q ∈ s, f q) = ∑ q ∈ s, dot x (f q) := by
  unfold dot
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem dr_smul (x y : Vec d) (c : ℝ) : dot x (c • y) = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dl_sub (x y z : Vec d) : dot (x - y) z = dot x z - dot y z := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

end

theorem mv_sum_l {κ ι Q : Type} [Fintype κ] [Fintype ι] (s : Finset Q) (A : Q → Matrix κ ι ℝ) (y : ι → ℝ) :
    (∑ k ∈ s, A k).mulVec y = ∑ k ∈ s, (A k).mulVec y :=
  map_sum (Matrix.mulVec.addMonoidHomLeft y) A s

theorem mv_sum_r {κ ι Q : Type} [Fintype κ] [Fintype ι] (s : Finset Q) (A : Matrix κ ι ℝ) (f : Q → ι → ℝ) :
    A.mulVec (∑ q ∈ s, f q) = ∑ q ∈ s, A.mulVec (f q) :=
  map_sum A.mulVecLin f s

theorem regroup {Q P : Type} [Fintype Q] [Fintype P] [DecidableEq P] {d : ℕ} (fq : Q → P) (f : Q → ℝ)
    (v : P → Vec d) :
    ∑ q, f q • v (fq q) = ∑ p, (∑ q, if fq q = p then f q else 0) • v p := by
  simp only [Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => by rw [Finset.sum_ite_eq]; simp

end Cl8

section
open Cl8

/-- MC-N.P2-8.1 (JST `Paper1.Spec.P2_8_1`, proof `Paper1.Proofs.p2_8_1`). P2-8.1: exact boundary entropy identity, and conservation `Σ_i b_i = Σ_q F*_q`. -/
theorem _root_.CFDLean.Num.quadratureClosure_entropy :
    ∀ (ι Q S κ : Type) [Fintype ι] [Fintype Q] [Fintype κ] (d : ℕ) (w : S → κ → ℝ) (ψ : S → Vec d)
      (Fec : S → S → Vec d → κ → ℝ) (u : ι → S) (φ : Q → ι → ℝ) (N : Q → Vec d) (ut : Q → S) (Fs : Q → κ → ℝ),
      (∀ a b y, Fec a b y = Fec b a y) →
      (∀ a b y, pairF (w b - w a) (Fec a b y) = dot (ψ b - ψ a) y) →
      (∀ q, ∑ k, φ q k = 1) → (∀ q, w (ut q) = ∑ k, φ q k • w (u k)) →
      let beta : ι → Vec d := fun i => ∑ q, φ q i • N q
      let b : ι → κ → ℝ := fun i => ∑ q, φ q i •
        (Fec (u i) (ut q) (N q) - ∑ k, φ q k • Fec (ut q) (u k) (N q) + Fs q)
      (∑ i, (dot (ψ (u i)) (beta i) - pairF (w (u i)) (b i))) =
        ∑ q, (dot (ψ (ut q)) (N q) - pairF (w (ut q)) (Fs q)) ∧
      ∑ i, b i = ∑ q, Fs q := by
  intro ι Q S κ _ _ _ d w ψ Fec u φ N ut Fs hsym htad hφ hw
  simp only []
  have hsw : ∀ q i, Fec (u i) (ut q) (N q) = Fec (ut q) (u i) (N q) := fun q i => hsym _ _ _
  simp only [hsw]
  -- `Σ_i φ_qi w_i · Y = w̃_q · Y`
  have hcomb : ∀ q (Y : κ → ℝ), ∑ i, φ q i * pairF (w (u i)) Y = pairF (w (ut q)) Y := by
    intro q Y
    rw [hw q, pl_sum]
    exact Finset.sum_congr rfl fun i _ => (pl_smul _ _ _).symm
  have pq : ∀ q, ∑ i, pairF (w (u i)) (φ q i • (Fec (ut q) (u i) (N q) -
      ∑ k, φ q k • Fec (ut q) (u k) (N q) + Fs q)) =
      ∑ k, φ q k * dot (ψ (u k)) (N q) - dot (ψ (ut q)) (N q) + pairF (w (ut q)) (Fs q) := by
    intro q
    have e1 : ∀ i, pairF (w (u i)) (φ q i • (Fec (ut q) (u i) (N q) -
        ∑ k, φ q k • Fec (ut q) (u k) (N q) + Fs q)) =
        φ q i * pairF (w (u i)) (Fec (ut q) (u i) (N q)) -
          φ q i * pairF (w (u i)) (∑ k, φ q k • Fec (ut q) (u k) (N q)) +
          φ q i * pairF (w (u i)) (Fs q) := by
      intro i
      rw [pr_smul, pr_add, pr_sub]
      ring
    simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, hcomb]
    have htk : ∀ k, φ q k * pairF (w (u k)) (Fec (ut q) (u k) (N q)) =
        φ q k * pairF (w (ut q)) (Fec (ut q) (u k) (N q)) + φ q k * dot (ψ (u k)) (N q) -
          φ q k * dot (ψ (ut q)) (N q) := by
      intro k
      have h := htad (ut q) (u k) (N q)
      rw [pl_sub, dl_sub] at h
      linear_combination φ q k * h
    simp only [htk, Finset.sum_add_distrib, Finset.sum_sub_distrib, pr_sum, pr_smul]
    rw [← Finset.sum_mul, hφ q]
    ring
  constructor
  · rw [Finset.sum_sub_distrib]
    have h1 : ∑ i, dot (ψ (u i)) (∑ q, φ q i • N q) = ∑ q, ∑ k, φ q k * dot (ψ (u k)) (N q) := by
      simp only [dr_sum, dr_smul]
      exact Finset.sum_comm
    have h2 : ∑ i, pairF (w (u i)) (∑ q, φ q i • (Fec (ut q) (u i) (N q) -
        ∑ k, φ q k • Fec (ut q) (u k) (N q) + Fs q)) =
        ∑ q, (∑ k, φ q k * dot (ψ (u k)) (N q) - dot (ψ (ut q)) (N q) + pairF (w (ut q)) (Fs q)) := by
      simp only [pr_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => pq q
    rw [h1, h2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_smul, hφ q,
      one_smul]
    abel

/-- MC-N.P2-8.2 (JST `Paper1.Spec.P2_8_2`, proof `Paper1.Proofs.p2_8_2`). P2-8.2 (free stream): a uniform state with `F*_q = F(u)·N_q` and `Σ_q φ_qi N_q = -Σ_k n_ik` has zero residual (the closure's free-stream property assumed in P1-2.7 is proved here). -/
theorem _root_.CFDLean.Num.quadratureClosure_freeStream :
    ∀ (ι Q S κ : Type) [Fintype ι] [Fintype Q] [Fintype κ] (d : ℕ) (Fec : S → S → Vec d → κ → ℝ)
      (phys : S → Vec d → κ → ℝ) (U : S) (φ : Q → ι → ℝ) (N : Q → Vec d) (n : ι → ι → Vec d),
      (∀ a b, IsLinearMap ℝ (Fec a b)) → (∀ y, Fec U U y = phys U y) → (∀ q, ∑ k, φ q k = 1) →
      (∀ i, ∑ q, φ q i • N q = -∑ k, n i k) →
      let b : ι → κ → ℝ := fun i => ∑ q, φ q i •
        (Fec U U (N q) - ∑ k, φ q k • Fec U U (N q) + phys U (N q))
      ∀ i, -(∑ k, Fec U U (n i k)) - b i = 0 := by
  intro ι Q S κ _ _ _ d Fec phys U φ N n hlin hcons hφ hbeta
  simp only []
  intro i
  let L : Vec d →ₗ[ℝ] (κ → ℝ) := IsLinearMap.mk' (Fec U U) (hlin U U)
  have hL : ∀ y, L y = Fec U U y := fun _ => rfl
  have hb : ∑ q, φ q i • (Fec U U (N q) - ∑ k, φ q k • Fec U U (N q) + phys U (N q)) =
      -∑ k, Fec U U (n i k) := by
    simp only [← Finset.sum_smul, hφ, one_smul, sub_self, zero_add, ← hcons]
    simp only [← hL, ← map_smul, ← map_sum, hbeta i, map_neg]
  rw [hb]
  abel

/-- MC-N.P2-8.3 (JST `Paper1.Spec.P2_8_3`, proof `Paper1.Proofs.p2_8_3`). P2-8.3 (linear fluxes): with `F^ec = ½(F_a + F_b)·y`, `F(ũ_q) = Σ_k φ_qk F_k` and `F*_q = F(ũ_q)·N_q`: `b_i = ½(F_i·β_i + Σ_k F_k·Σ_q φ_qi φ_qk N_q)`. -/
theorem _root_.CFDLean.Num.quadratureClosure_linear :
    ∀ (ι Q S κ : Type) [Fintype ι] [Fintype Q] [Fintype κ] (d : ℕ) (Fec : S → S → Vec d → κ → ℝ)
      (Fl : S → Matrix κ (Fin d) ℝ) (u : ι → S) (φ : Q → ι → ℝ) (N : Q → Vec d) (ut : Q → S),
      (∀ a b y, Fec a b y = ((1 / 2 : ℝ) • (Fl a + Fl b)).mulVec y) →
      (∀ q, Fl (ut q) = ∑ k, φ q k • Fl (u k)) → (∀ q, ∑ k, φ q k = 1) →
      let beta : ι → Vec d := fun i => ∑ q, φ q i • N q
      let b : ι → κ → ℝ := fun i => ∑ q, φ q i •
        (Fec (u i) (ut q) (N q) - ∑ k, φ q k • Fec (ut q) (u k) (N q) + (Fl (ut q)).mulVec (N q))
      ∀ i, b i = (1 / 2 : ℝ) • ((Fl (u i)).mulVec (beta i) +
        ∑ k, (Fl (u k)).mulVec (∑ q, (φ q i * φ q k) • N q)) := by
  intro ι Q S κ _ _ _ d Fec Fl u φ N ut hec hFl hφ
  simp only []
  intro i
  simp only [hec, Matrix.smul_mulVec, Matrix.add_mulVec, mv_sum_r, Matrix.mulVec_smul]
  have ha : ∀ q c, (Fl (ut q)).mulVec (N q) c = ∑ k, φ q k * (Fl (u k)).mulVec (N q) c := by
    intro q c
    rw [hFl q, mv_sum_l, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_mulVec]; rfl
  funext c
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  have hin : ∀ q, ∑ k, φ q k * (1 / 2 * ((Fl (ut q)).mulVec (N q) c + (Fl (u k)).mulVec (N q) c)) =
      (Fl (ut q)).mulVec (N q) c := by
    intro q
    simp only [mul_add, Finset.sum_add_distrib]
    have e1 : ∑ k, φ q k * (1 / 2 * (Fl (ut q)).mulVec (N q) c) = 1 / 2 * (Fl (ut q)).mulVec (N q) c := by
      rw [← Finset.sum_mul, hφ q, one_mul]
    have e2 : ∑ k, φ q k * (1 / 2 * (Fl (u k)).mulVec (N q) c) = 1 / 2 * (Fl (ut q)).mulVec (N q) c := by
      rw [ha q c, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2]; ring
  simp only [hin]
  have e3 : ∑ k, ∑ q, φ q i * φ q k * (Fl (u k)).mulVec (N q) c =
      ∑ q, φ q i * (Fl (ut q)).mulVec (N q) c := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ha q c, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e3, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- MC-N.P2-8.4 (JST `Paper1.Spec.P2_8_4`, proof `Paper1.Proofs.p2_8_4`). P2-8.4: a face rule with (H1), (H2) on every boundary facet of a conforming mesh gives `Σ_q φ_qi N_q = β_i` and `Σ_q φ_qi φ_qk N_q = B_c ik`; so P2-8.3 is the closure of `lem:bdefect`. -/
theorem _root_.CFDLean.Num.WMesh.faceRule_beta_B :
    ∀ (ι C Q : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C] [Fintype Q] (d : ℕ) (M : WMesh ι C d)
      (bd : C × Fin (d + 1) → Bool) (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ) (φ : Q → ι → ℝ),
      M.Valid → 1 ≤ d → M.Conforming bd → (∀ q, bd (fq q) = true) →
      (∀ q k, k ∉ M.facetNodes (fq q) → φ q k = 0) →
      (∀ p, bd p = true → ∀ i ∈ M.facetNodes p,
        (∑ q, if fq q = p then aq q * φ q i else 0) = 1 / (d : ℝ)) →
      (∀ p, bd p = true → ∀ i ∈ M.facetNodes p, ∀ k ∈ M.facetNodes p,
        (∑ q, if fq q = p then aq q * φ q i * φ q k else 0) = (1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) →
      let N : Q → Vec d := fun q => aq q • M.areaVec (fq q)
      (∀ i, ∑ q, φ q i • N q = M.beta i) ∧ (∀ i k, ∑ q, (φ q i * φ q k) • N q = M.B i k) := by
  intro ι C Q _ _ _ _ _ d M bd fq aq φ hV hd hC hbdq hφz hH1 hH2
  simp only []
  obtain ⟨hβ, hB, _⟩ := WMesh.conforming_boundary ι C d M bd hV hd hC
  have hzero : ∀ p (f : Q → ℝ), (∀ q, fq q = p → f q = 0) → (∑ q, if fq q = p then f q else 0) = 0 :=
    fun p f hf => Finset.sum_eq_zero fun q _ => by split_ifs with h <;> simp [hf q, h]
  constructor
  · intro i
    rw [hβ i]
    have e : ∀ q, φ q i • (aq q • M.areaVec (fq q)) = (aq q * φ q i) • M.areaVec (fq q) := fun q => by
      rw [smul_smul, mul_comm]
    simp only [e]
    rw [regroup]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : bd p = true ∧ i ∈ M.facetNodes p
    · rw [ite_eq_left hp, hH1 p hp.1 i hp.2]
    · rw [ite_eq_right hp]
      have : (∑ q, if fq q = p then aq q * φ q i else 0) = 0 := by
        refine hzero p _ fun q hq => ?_
        by_cases hb : bd p = true
        · have hi : i ∉ M.facetNodes (fq q) := by rw [hq]; exact fun h => hp ⟨hb, h⟩
          rw [hφz q i hi, mul_zero]
        · exact absurd (hq ▸ hbdq q) hb
      rw [this, zero_smul]
  · intro i k
    rw [hB i k]
    have e : ∀ q, (φ q i * φ q k) • (aq q • M.areaVec (fq q)) =
        (aq q * φ q i * φ q k) • M.areaVec (fq q) := fun q => by
      rw [smul_smul]; ring_nf
    simp only [e]
    rw [regroup]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : bd p = true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p
    · rw [ite_eq_left hp, hH2 p hp.1 i hp.2.1 k hp.2.2]
    · rw [ite_eq_right hp]
      have : (∑ q, if fq q = p then aq q * φ q i * φ q k else 0) = 0 := by
        refine hzero p _ fun q hq => ?_
        by_cases hb : bd p = true
        · by_cases hi : i ∈ M.facetNodes p
          · have hk : k ∉ M.facetNodes (fq q) := by rw [hq]; exact fun h => hp ⟨hb, hi, h⟩
            rw [hφz q k hk, mul_zero]
          · have hi' : i ∉ M.facetNodes (fq q) := by rw [hq]; exact hi
            rw [hφz q i hi', mul_zero, zero_mul]
        · exact absurd (hq ▸ hbdq q) hb
      rw [this, zero_smul]

end

end CFDLean.Num.Internal
