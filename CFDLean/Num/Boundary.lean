import CFDLean.Num.Mesh
set_option cleanup.letToHave false -- MC-N: keep the `let` binders of the moved JST definitions and statements
set_option linter.unusedSectionVars false

/-! Boundary facets of a weighted simplex mesh: conforming meshes, facet balance and side balance; closure from a
facet pairing (P1-5.0a), boundary sums of `β` and `B_c` (P2-6.3, P3-11.1), side balance implies facet balance
(P3-11.4, P3-11.4b).

MC-N: definitions moved verbatim from JST_Paper_Lean `NumCore/Boundary.lean` (except `EW`, in `CFDLean.Num.Mesh`),
`NumCore/Balance.lean` and `Paper1/Spec/Item11b.lean` (`facetSide`, `SideBalanced`, `facetSide2`, `SideBalanced2`);
proofs from `Paper1/Proofs/{Closure,Item6,Item11a,Item11b}.lean`. -/
noncomputable section
open scoped BigOperators
namespace CFDLean.Num

namespace WMesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

/-- Global facet pairing: every facet `p = (T, o)` not marked as boundary (`bd p = false`) is matched with another
non-boundary facet with the same vertex set, the same weight and the opposite area vector (a conforming mesh). -/
def Conforming (bd : C × Fin (d + 1) → Bool) : Prop :=
  ∃ σ : C × Fin (d + 1) → C × Fin (d + 1), ∀ p, bd p = false →
    σ (σ p) = p ∧ σ p ≠ p ∧ bd (σ p) = false ∧ M.facetNodes (σ p) = M.facetNodes p ∧
      M.ω (σ p).1 = M.ω p.1 ∧ M.facetVec (σ p) = -M.facetVec p

/-- Weighted area vector `A_f N_f` of a facet. -/
def areaVec (p : C × Fin (d + 1)) : Vec d := M.ω p.1 • M.facetVec p

def FacetBalanced (bd : C × Fin (d + 1) → Bool) : Prop :=
  ∀ S : Finset ι, ∑ p, (if bd p = false ∧ M.facetNodes p = S then M.areaVec p else 0) = 0

end WMesh

/-- Side of a facet `p = (T, o)` relative to its sorted vertex triple `a < b < c`: the sign of
`(x_b - x_a) × (x_c - x_a) · (x_o - x_a)`. -/
def facetSide {ι C : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype C] (M : WMesh ι C 3)
    (p : C × Fin 4) : ℝ :=
  let l := (M.facetNodes p).sort (· ≤ ·)
  let xa := M.pos (l.getD 0 (M.vert p.1 p.2))
  let xb := M.pos (l.getD 1 (M.vert p.1 p.2))
  let xc := M.pos (l.getD 2 (M.vert p.1 p.2))
  SignType.sign (dot (cross3 (xb - xa) (xc - xa)) (M.pos (M.vert p.1 p.2) - xa))

/-- Side balance: for every vertex set, the weights of the interior facets on the two sides are equal. -/
def SideBalanced {ι C : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype C] (M : WMesh ι C 3)
    (bd : C × Fin 4 → Bool) : Prop :=
  ∀ S : Finset ι, ∑ p, (if bd p = false ∧ M.facetNodes p = S then M.ω p.1 * facetSide M p else 0) = 0

/-- Side of a 2D facet relative to its sorted vertex pair `a < b`. -/
def facetSide2 {ι C : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype C] (M : WMesh ι C 2)
    (p : C × Fin 3) : ℝ :=
  let l := (M.facetNodes p).sort (· ≤ ·)
  let xa := M.pos (l.getD 0 (M.vert p.1 p.2))
  let xb := M.pos (l.getD 1 (M.vert p.1 p.2))
  SignType.sign (dot (perp2 (xb - xa)) (M.pos (M.vert p.1 p.2) - xa))

def SideBalanced2 {ι C : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype C] (M : WMesh ι C 2)
    (bd : C × Fin 3 → Bool) : Prop :=
  ∀ S : Finset ι, ∑ p, (if bd p = false ∧ M.facetNodes p = S then M.ω p.1 * facetSide2 M p else 0) = 0

end CFDLean.Num

namespace CFDLean.Num.Internal

namespace Closure
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

/-- P1-5.0a without the validity hypothesis (the identity is purely algebraic). -/
theorem closed_of_facetPaired (i : ι) (h : M.FacetPaired i) : M.Closed i := by
  intro k
  obtain ⟨σ, hσ⟩ := h
  set P : C × Fin (d + 1) → Prop := fun p => i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p with hP
  have hS : ∑ p : C × Fin (d + 1), (if P p then M.ω p.1 • M.facetVec p else 0) = 0 := by
    rw [← Finset.sum_filter]
    have hmem : ∀ p, p ∈ Finset.univ.filter P → P (σ p) ∧ i ∈ M.facetNodes p := by
      intro p hp
      have hp' : P p := (Finset.mem_filter.mp hp).2
      have hs := hσ p hp'.1
      refine ⟨?_, hp'.1⟩
      show i ∈ M.facetNodes (σ p) ∧ k ∈ M.facetNodes (σ p)
      rw [hs.2.2.1]
      exact hp'
    refine Finset.sum_involution (fun p _ => σ p) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨-, -, -, hω, hv⟩ := hσ p (hmem p hp).2
      rw [hω, hv, smul_neg, add_neg_cancel]
    · intro p hp _
      exact (hσ p (hmem p hp).2).2.1
    · intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem p hp).1⟩
    · intro p hp
      exact (hσ p (hmem p hp).2).1
  have key : ((d : ℝ) * ((d : ℝ) + 1)) • M.B i k = 0 := by
    rw [B_eq, Finset.smul_sum]
    calc
      _ = ∑ T, M.ω T • ((if i = k then (2 : ℝ) else 1) •
            ∑ o, if i ∈ M.facetNodes (T, o) ∧ k ∈ M.facetNodes (T, o) then M.facetVec (T, o) else 0) := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [← cell_identity, smul_comm]
          congr 1
          simp only [Finset.smul_sum, smul_ite, smul_zero]
      _ = (if i = k then (2 : ℝ) else 1) •
            ∑ p : C × Fin (d + 1), (if P p then M.ω p.1 • M.facetVec p else 0) := by
          rw [Fintype.sum_prod_type, Finset.smul_sum]
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [smul_comm, Finset.smul_sum]
          congr 1
          funext o
          simp only [hP, smul_ite, smul_zero]
      _ = 0 := by rw [hS, smul_zero]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    funext α
    exact α.elim0
  · have hne : ((d : ℝ) * ((d : ℝ) + 1)) ≠ 0 := by positivity
    exact (smul_eq_zero.mp key).resolve_left hne

end Closure

/-- MC-N.P1-5.0a (JST `Paper1.Spec.P1_5_0a`, proof `Paper1.Proofs.p1_5_0a`). P1-5.0a: a facet pairing at `i` makes `i` a closed (interior) vertex. -/
theorem _root_.CFDLean.Num.WMesh.closed_of_facetPaired :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d) (i : ι),
      M.Valid → M.FacetPaired i → M.Closed i := by
  intro ι C _ _ _ d M i _hV h
  exact Closure.closed_of_facetPaired M i h

namespace Sbp6

section Mesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

/-- Facets of all cells containing `i` and `k`: `d(d+1) B_ik = (1 + δ_ik) Σ_p [i,k ∈ p] A_p`. -/
theorem B_facets (i k : ι) : ((d : ℝ) * ((d : ℝ) + 1)) • M.B i k =
    (if i = k then (2 : ℝ) else 1) •
      ∑ p : C × Fin (d + 1), (if i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then M.areaVec p else 0) := by
  rw [Closure.B_eq, Finset.smul_sum]
  calc
    _ = ∑ T, M.ω T • ((if i = k then (2 : ℝ) else 1) •
          ∑ o, if i ∈ M.facetNodes (T, o) ∧ k ∈ M.facetNodes (T, o) then M.facetVec (T, o) else 0) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [← Closure.cell_identity, smul_comm]
        congr 1
        simp only [Finset.smul_sum, smul_ite, smul_zero]
    _ = _ := by
        rw [Fintype.sum_prod_type, Finset.smul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [smul_comm, Finset.smul_sum]
        congr 1
        funext o
        simp only [WMesh.areaVec, smul_ite, smul_zero]

/-- Interior facets cancel in pairs. -/
theorem interior_zero (bd : C × Fin (d + 1) → Bool) (hC : M.Conforming bd) (P : Finset ι → Prop)
    [DecidablePred P] :
    ∑ p : C × Fin (d + 1), (if bd p = false ∧ P (M.facetNodes p) then M.areaVec p else 0) = 0 := by
  obtain ⟨σ, hσ⟩ := hC
  rw [← Finset.sum_filter]
  have hmem : ∀ p, p ∈ Finset.univ.filter (fun p => bd p = false ∧ P (M.facetNodes p)) →
      bd p = false ∧ P (M.facetNodes (σ p)) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    refine ⟨hp'.1, ?_⟩
    rw [(hσ p hp'.1).2.2.2.1]
    exact hp'.2
  refine Finset.sum_involution (fun p _ => σ p) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨-, -, -, -, hω, hv⟩ := hσ p (hmem p hp).1
    simp only [WMesh.areaVec]
    rw [hω, hv, smul_neg, add_neg_cancel]
  · intro p hp _
    exact (hσ p (hmem p hp).1).2.1
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hσ p (hmem p hp).1).2.2.1, (hmem p hp).2⟩
  · intro p hp
    exact (hσ p (hmem p hp).1).1

theorem split_bd {X : Type} [AddCommGroup X] (bd : C × Fin (d + 1) → Bool) (Q : C × Fin (d + 1) → Prop)
    [DecidablePred Q] (f : C × Fin (d + 1) → X) :
    ∑ p, (if Q p then f p else 0) =
      (∑ p, if bd p = true ∧ Q p then f p else 0) + ∑ p, if bd p = false ∧ Q p then f p else 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  cases bd p <;> simp

theorem card_facetNodes (p : C × Fin (d + 1)) : (M.facetNodes p).card = d := by
  simp [WMesh.facetNodes, Finset.card_erase_of_mem]

theorem B_bd (bd : C × Fin (d + 1) → Bool) (hC : M.Conforming bd) (hd : 1 ≤ d) (i k : ι) :
    M.B i k = ∑ p, if bd p ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
        ((1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) • M.areaVec p else 0 := by
  have h := B_facets M i k
  rw [split_bd bd (fun p => i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p) M.areaVec] at h
  have h0 := interior_zero M bd hC (fun s => i ∈ s ∧ k ∈ s)
  rw [h0, add_zero] at h
  have hne : ((d : ℝ) * ((d : ℝ) + 1)) ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hB : M.B i k = (((d : ℝ) * ((d : ℝ) + 1))⁻¹ * (if i = k then (2 : ℝ) else 1)) •
      ∑ p, (if bd p = true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then M.areaVec p else 0) := by
    rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hB, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_ite, smul_zero]
  congr 1
  congr 1
  split_ifs <;> ring

theorem beta_bd (bd : C × Fin (d + 1) → Bool) (hC : M.Conforming bd) (hd : 1 ≤ d) (i : ι) :
    M.beta i = ∑ p, if bd p ∧ i ∈ M.facetNodes p then (1 / (d : ℝ)) • M.areaVec p else 0 := by
  rw [← B_row, Finset.sum_congr rfl fun k _ => B_bd M bd hC hd i k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : bd p = true ∧ i ∈ M.facetNodes p
  · rw [ite_eq_left hp]
    have e : ∀ k, (if bd p = true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
        ((1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) • M.areaVec p else 0) =
        (if k ∈ M.facetNodes p then (1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1)) else 0) •
          M.areaVec p := by
      intro k
      by_cases hk : k ∈ M.facetNodes p
      · simp [hp.1, hp.2, hk]
      · simp [hk]
    rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.sum_smul, ← Finset.sum_filter]
    congr 1
    have hfil : Finset.univ.filter (fun k => k ∈ M.facetNodes p) = M.facetNodes p := by
      ext k; simp
    rw [hfil, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left hp.2]
    simp only [Finset.sum_const, card_facetNodes, nsmul_eq_mul, mul_one]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    field_simp
  · rw [ite_eq_right hp]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [ite_eq_right]
    exact fun h => hp ⟨h.1, h.2.1⟩

end Mesh
end Sbp6

section
open Sbp6

/-- MC-N.P2-6.3 (JST `Paper1.Spec.P2_6_3`, proof `Paper1.Proofs.p2_6_3`). P2-6.3: on a conforming mesh, `β` and the boundary mass matrix `B_c = c + cᵀ` are sums over the boundary facets; a vertex on no boundary facet is closed. -/
theorem _root_.CFDLean.Num.WMesh.conforming_boundary :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d)
      (bd : C × Fin (d + 1) → Bool), M.Valid → 1 ≤ d → M.Conforming bd →
      (∀ i, M.beta i = ∑ p, if bd p ∧ i ∈ M.facetNodes p then (1 / (d : ℝ)) • M.areaVec p else 0) ∧
      (∀ i k, M.B i k = ∑ p, if bd p ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
          ((1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) • M.areaVec p else 0) ∧
      (∀ i, (∀ p, bd p = true → i ∉ M.facetNodes p) → M.Closed i) := by
  intro ι C _ _ _ d M bd _hM hd hC
  refine ⟨beta_bd M bd hC hd, B_bd M bd hC hd, ?_⟩
  intro i hi k
  rw [B_bd M bd hC hd]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [ite_eq_right]
  rintro ⟨h1, h2, -⟩
  exact hi p h1 h2

end

namespace Avg11

section Mesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

/-- Conforming meshes are facet balanced (pairing involution restricted to one vertex set). -/
theorem conforming_balanced (bd : C × Fin (d + 1) → Bool) (hC : M.Conforming bd) : M.FacetBalanced bd :=
  fun S => Sbp6.interior_zero M bd hC (fun s => s = S)

/-- Interior facets cancel on a facet-balanced mesh: group them by vertex set. -/
theorem interior_zero (bd : C × Fin (d + 1) → Bool) (hB : M.FacetBalanced bd) (P : Finset ι → Prop)
    [DecidablePred P] :
    ∑ p : C × Fin (d + 1), (if bd p = false ∧ P (M.facetNodes p) then M.areaVec p else 0) = 0 := by
  have e : ∀ p : C × Fin (d + 1), (if bd p = false ∧ P (M.facetNodes p) then M.areaVec p else 0) =
      ∑ S : Finset ι, if M.facetNodes p = S then
        (if bd p = false ∧ P (M.facetNodes p) then M.areaVec p else 0) else 0 := by
    intro p
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun p _ => e p, Finset.sum_comm]
  refine Finset.sum_eq_zero fun S _ => ?_
  by_cases hS : P S
  · refine (Finset.sum_congr rfl fun p _ => ?_).trans (hB S)
    by_cases hp : M.facetNodes p = S
    · subst hp
      simp [hS]
    · simp [hp]
  · refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : M.facetNodes p = S
    · subst hp
      simp [hS]
    · simp [hp]

theorem B_bd (bd : C × Fin (d + 1) → Bool) (hF : M.FacetBalanced bd) (hd : 1 ≤ d) (i k : ι) :
    M.B i k = ∑ p, if bd p ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
        ((1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) • M.areaVec p else 0 := by
  have h := Sbp6.B_facets M i k
  rw [Sbp6.split_bd bd (fun p => i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p) M.areaVec] at h
  have h0 := interior_zero M bd hF (fun s => i ∈ s ∧ k ∈ s)
  rw [h0, add_zero] at h
  have hne : ((d : ℝ) * ((d : ℝ) + 1)) ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hB : M.B i k = (((d : ℝ) * ((d : ℝ) + 1))⁻¹ * (if i = k then (2 : ℝ) else 1)) •
      ∑ p, (if bd p = true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then M.areaVec p else 0) := by
    rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hB, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_ite, smul_zero]
  congr 1
  congr 1
  split_ifs <;> ring

theorem beta_bd (bd : C × Fin (d + 1) → Bool) (hF : M.FacetBalanced bd) (hd : 1 ≤ d) (i : ι) :
    M.beta i = ∑ p, if bd p ∧ i ∈ M.facetNodes p then (1 / (d : ℝ)) • M.areaVec p else 0 := by
  rw [← Sbp6.B_row, Finset.sum_congr rfl fun k _ => B_bd M bd hF hd i k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : bd p = true ∧ i ∈ M.facetNodes p
  · rw [ite_eq_left hp]
    have e : ∀ k, (if bd p = true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
        ((1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) • M.areaVec p else 0) =
        (if k ∈ M.facetNodes p then (1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1)) else 0) •
          M.areaVec p := by
      intro k
      by_cases hk : k ∈ M.facetNodes p
      · simp [hp.1, hp.2, hk]
      · simp [hk]
    rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.sum_smul, ← Finset.sum_filter]
    congr 1
    have hfil : Finset.univ.filter (fun k => k ∈ M.facetNodes p) = M.facetNodes p := by
      ext k; simp
    rw [hfil, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left hp.2]
    simp only [Finset.sum_const, Sbp6.card_facetNodes, nsmul_eq_mul, mul_one]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    field_simp
  · rw [ite_eq_right hp]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [ite_eq_right]
    exact fun h => hp ⟨h.1, h.2.1⟩

end Mesh
end Avg11

section
open Avg11

/-- MC-N.P3-11.1 (JST `Paper1.Spec.P3_11_1`, proof `Paper1.Proofs.p3_11_1`). P3-11.1: on a facet-balanced mesh (any weights), `β` and `B_c` are sums over the boundary facets, and a vertex on no boundary facet is closed. A conforming mesh (P2-6.3) is facet balanced. -/
theorem _root_.CFDLean.Num.WMesh.facetBalanced_boundary :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d)
      (bd : C × Fin (d + 1) → Bool), M.Valid → 1 ≤ d →
      (M.Conforming bd → M.FacetBalanced bd) ∧
      (M.FacetBalanced bd →
        (∀ i, M.beta i = ∑ p, if bd p ∧ i ∈ M.facetNodes p then (1 / (d : ℝ)) • M.areaVec p else 0) ∧
        (∀ i k, M.B i k = ∑ p, if bd p ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
            ((1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) • M.areaVec p else 0) ∧
        (∀ i, (∀ p, bd p = true → i ∉ M.facetNodes p) → M.Closed i)) := by
  intro ι C _ _ _ d M bd _hM hd
  refine ⟨conforming_balanced M bd, fun hF => ⟨beta_bd M bd hF hd, B_bd M bd hF hd, ?_⟩⟩
  intro i hi k
  rw [B_bd M bd hF hd]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [ite_eq_right]
  rintro ⟨h1, h2, -⟩
  exact hi p h1 h2

end

namespace Avg11b
open Geo3

section Mesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype C]

theorem mem_facetNodes {d : ℕ} (M : WMesh ι C d) (p : C × Fin (d + 1)) (i : ι) :
    i ∈ M.facetNodes p ↔ ∃ a, a ≠ p.2 ∧ M.vert p.1 a = i := by
  simp only [WMesh.facetNodes, Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true]

theorem card_facetNodes {d : ℕ} (M : WMesh ι C d) (p : C × Fin (d + 1)) : (M.facetNodes p).card = d := by
  simp [WMesh.facetNodes, Finset.card_erase_of_mem]

theorem locals3 (M : WMesh ι C 3) (p : C × Fin 4) (i0 i1 i2 : ι)
    (hl : (M.facetNodes p).sort (· ≤ ·) = [i0, i1, i2]) :
    ∃ a b c : Fin 4, [p.2, a, b, c].Nodup ∧ M.vert p.1 a = i0 ∧ M.vert p.1 b = i1 ∧ M.vert p.1 c = i2 := by
  have hnd : [i0, i1, i2].Nodup := hl ▸ Finset.sort_nodup _ _
  have hm : ∀ i ∈ [i0, i1, i2], ∃ a, a ≠ p.2 ∧ M.vert p.1 a = i := by
    intro i hi
    rw [← hl, Finset.mem_sort] at hi
    exact (mem_facetNodes M p i).mp hi
  obtain ⟨a, ha, rfl⟩ := hm i0 (by simp)
  obtain ⟨b, hb, rfl⟩ := hm i1 (by simp)
  obtain ⟨c, hc, rfl⟩ := hm i2 (by simp)
  refine ⟨a, b, c, ?_, rfl, rfl, rfl⟩
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true, EmbeddingLike.apply_eq_iff_eq] at hnd ⊢
  exact ⟨⟨Ne.symm ha, Ne.symm hb, Ne.symm hc⟩, hnd⟩

theorem locals2 (M : WMesh ι C 2) (p : C × Fin 3) (i0 i1 : ι)
    (hl : (M.facetNodes p).sort (· ≤ ·) = [i0, i1]) :
    ∃ a b : Fin 3, [p.2, a, b].Nodup ∧ M.vert p.1 a = i0 ∧ M.vert p.1 b = i1 := by
  have hnd : [i0, i1].Nodup := hl ▸ Finset.sort_nodup _ _
  have hm : ∀ i ∈ [i0, i1], ∃ a, a ≠ p.2 ∧ M.vert p.1 a = i := by
    intro i hi
    rw [← hl, Finset.mem_sort] at hi
    exact (mem_facetNodes M p i).mp hi
  obtain ⟨a, ha, rfl⟩ := hm i0 (by simp)
  obtain ⟨b, hb, rfl⟩ := hm i1 (by simp)
  refine ⟨a, b, ?_, rfl, rfl⟩
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true, EmbeddingLike.apply_eq_iff_eq] at hnd ⊢
  exact ⟨⟨Ne.symm ha, Ne.symm hb⟩, hnd⟩

theorem simplex_x {d : ℕ} (M : WMesh ι C d) (T : C) (e : Fin (d + 1)) :
    (M.simplex T).x e = M.pos (M.vert T e) := rfl

/-- 3D: the facet vector is `-½ · side · nv` of the sorted vertex triple. -/
theorem facetVec_side (M : WMesh ι C 3) (hM : M.Valid) (p : C × Fin 4) (i0 i1 i2 : ι)
    (hl : (M.facetNodes p).sort (· ≤ ·) = [i0, i1, i2]) :
    M.facetVec p = (-(1 / 2) * facetSide M p) • cross3 (M.pos i1 - M.pos i0) (M.pos i2 - M.pos i0) := by
  obtain ⟨a, b, c, hnd, ha, hb, hc⟩ := locals3 M p i0 i1 i2 hl
  have hT := hM.2 p.1
  have hf := facet_cross (M.simplex p.1) p.2 a b c hT hnd
  have htp := triple_perm (M.simplex p.1).x p.2 a b c hnd
  have hdet := det_edge3 (M.simplex p.1)
  simp only [simplex_x, ha, hb, hc] at hf htp hdet
  have hD0 : dot (cross3 (M.pos i1 - M.pos i0) (M.pos i2 - M.pos i0)) (M.pos (M.vert p.1 p.2) - M.pos i0) ≠ 0 := by
    intro h0
    apply hT
    rw [hdet]
    rcases htp with h | h
    · rw [← h, h0]
    · rw [h0] at h
      linarith
  rw [WMesh.facetVec, hf]
  simp only [facetSide, hl, List.getD_cons_zero, List.getD_cons_succ]
  congr 1
  rcases lt_or_gt_of_ne hD0 with h | h
  · rw [ite_eq_right (not_lt.mpr h.le), sign_neg h]; norm_num
  · rw [ite_eq_left h, sign_pos h]; norm_num

/-- 2D: the facet vector is `-side · perp2` of the sorted vertex pair. -/
theorem facetVec_side2 (M : WMesh ι C 2) (hM : M.Valid) (p : C × Fin 3) (i0 i1 : ι)
    (hl : (M.facetNodes p).sort (· ≤ ·) = [i0, i1]) :
    M.facetVec p = (-facetSide2 M p) • perp2 (M.pos i1 - M.pos i0) := by
  obtain ⟨a, b, hnd, ha, hb⟩ := locals2 M p i0 i1 hl
  have hT := hM.2 p.1
  have hf := facet_perp (M.simplex p.1) p.2 a b hT hnd
  have htp := triple_perm2 (M.simplex p.1).x p.2 a b hnd
  have hdet := det_edge2 (M.simplex p.1)
  simp only [simplex_x, ha, hb] at hf htp hdet
  have hD0 : dot (perp2 (M.pos i1 - M.pos i0)) (M.pos (M.vert p.1 p.2) - M.pos i0) ≠ 0 := by
    intro h0
    apply hT
    rw [hdet]
    rcases htp with h | h
    · rw [← h, h0, neg_zero]
    · rw [h0] at h
      linarith
  rw [WMesh.facetVec, hf]
  simp only [facetSide2, hl, List.getD_cons_zero, List.getD_cons_succ]
  congr 1
  rcases lt_or_gt_of_ne hD0 with h | h
  · rw [ite_eq_right (not_lt.mpr h.le), sign_neg h]; norm_num
  · rw [ite_eq_left h, sign_pos h]; norm_num

end Mesh
end Avg11b

section
open Avg11b

/-- MC-N.P3-11.4 (JST `Paper1.Spec.P3_11_4`, proof `Paper1.Proofs.p3_11_4`). P3-11.4 (d = 3): on a mesh of nondegenerate tetrahedra, side balance implies facet balance (each facet vector is `∓½` of the cross product of its sorted triangle, by P3-11.2). -/
theorem _root_.CFDLean.Num.WMesh.facetBalanced_of_sideBalanced :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype C] (M : WMesh ι C 3)
      (bd : C × Fin 4 → Bool), M.Valid → SideBalanced M bd → M.FacetBalanced bd := by
  intro ι C _ _ _ _ M bd hM hS S
  by_cases h3 : ∃ i0 i1 i2, S.sort (· ≤ ·) = [i0, i1, i2]
  · obtain ⟨i0, i1, i2, hl⟩ := h3
    have e : ∀ p, (if bd p = false ∧ M.facetNodes p = S then M.areaVec p else 0) =
        (if bd p = false ∧ M.facetNodes p = S then M.ω p.1 * facetSide M p else 0) •
          ((-(1 / 2) : ℝ) • cross3 (M.pos i1 - M.pos i0) (M.pos i2 - M.pos i0)) := by
      intro p
      split_ifs with h
      · rw [WMesh.areaVec, facetVec_side M hM p i0 i1 i2 (by rw [h.2]; exact hl), smul_smul, smul_smul]
        congr 1
        ring
      · rw [zero_smul]
    rw [Finset.sum_congr rfl fun p _ => e p, ← Finset.sum_smul, hS S, zero_smul]
  · refine Finset.sum_eq_zero fun p _ => ite_eq_right ?_
    rintro ⟨-, hp⟩
    apply h3
    apply List.length_eq_three.mp
    rw [Finset.length_sort, ← hp, card_facetNodes]

/-- MC-N.P3-11.4b (JST `Paper1.Spec.P3_11_4b`, proof `Paper1.Proofs.p3_11_4b`). P3-11.4b (d = 2): side balance implies facet balance. -/
theorem _root_.CFDLean.Num.WMesh.facetBalanced_of_sideBalanced2 :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype C] (M : WMesh ι C 2)
      (bd : C × Fin 3 → Bool), M.Valid → SideBalanced2 M bd → M.FacetBalanced bd := by
  intro ι C _ _ _ _ M bd hM hS S
  by_cases h2 : ∃ i0 i1, S.sort (· ≤ ·) = [i0, i1]
  · obtain ⟨i0, i1, hl⟩ := h2
    have e : ∀ p, (if bd p = false ∧ M.facetNodes p = S then M.areaVec p else 0) =
        (if bd p = false ∧ M.facetNodes p = S then M.ω p.1 * facetSide2 M p else 0) •
          (-perp2 (M.pos i1 - M.pos i0)) := by
      intro p
      split_ifs with h
      · rw [WMesh.areaVec, facetVec_side2 M hM p i0 i1 (by rw [h.2]; exact hl), smul_smul, smul_neg,
          ← neg_smul]
        congr 1
        ring
      · rw [zero_smul]
    rw [Finset.sum_congr rfl fun p _ => e p, ← Finset.sum_smul, hS S, zero_smul]
  · refine Finset.sum_eq_zero fun p _ => ite_eq_right ?_
    rintro ⟨-, hp⟩
    apply h2
    apply List.length_eq_two.mp
    rw [Finset.length_sort, ← hp, card_facetNodes]

end

end CFDLean.Num.Internal
