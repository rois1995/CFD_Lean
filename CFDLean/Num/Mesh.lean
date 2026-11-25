import CFDLean.Num.Simplex
set_option cleanup.letToHave false -- MC-N: keep the `let` binders of the moved JST definitions and statements
set_option linter.unusedSectionVars false

/-! A finite family of weighted simplices (simplex mesh: weights 1; split sub-simplices of a mixed mesh:
weights ω_s) and its median-dual P1 operator (`W_a^T = m_T = |T|/(d+1)`). Validity is a separate predicate.
Row and column sums and `β` (P1-2.3), SBP form and defect (P2-6.1, P2-6.2), dissipation geometry (P1-5.2 to P1-5.4)
and the dissipation tensor (P2-7.1 to P2-7.3).

MC-N: definitions moved verbatim from JST_Paper_Lean `NumCore/WMesh.lean` and, for the defect `EW`, from
`NumCore/Boundary.lean`; proofs from `Paper1/Proofs/{MeshAlgebra,Closure,Item6,DissGeom,Item7}.lean`. -/
noncomputable section
open scoped BigOperators
namespace CFDLean.Num

structure WMesh (ι C : Type) (d : ℕ) where
  pos : ι → Vec d
  vert : C → Fin (d + 1) ↪ ι
  ω : C → ℝ

namespace WMesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

def simplex (T : C) : Simplex d := ⟨fun a => M.pos (M.vert T a)⟩
def g (T : C) (a : Fin (d + 1)) : Vec d := (M.simplex T).grad a
def vol (T : C) : ℝ := (M.simplex T).vol
def m (T : C) : ℝ := M.vol T / ((d : ℝ) + 1)

/-- Nonnegative weights and nondegenerate cells. -/
def Valid : Prop := (∀ T, 0 ≤ M.ω T) ∧ ∀ T, (M.simplex T).Nondeg

/-- P1 operator of a general dual with weights `W T a` (`c_ik = Σ_{T∋i,k} W_i^T g_k^T`). -/
def cW (W : C → Fin (d + 1) → ℝ) (i k : ι) : Vec d :=
  ∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then (M.ω T * W T a) • M.g T b else 0

def nW (W : C → Fin (d + 1) → ℝ) (i k : ι) : Vec d := M.cW W i k - M.cW W k i

/-- Median dual. -/
def c (i k : ι) : Vec d := M.cW (fun T _ => M.m T) i k
def n (i k : ι) : Vec d := M.c i k - M.c k i
def B (i k : ι) : Vec d := M.c i k + M.c k i
def V (i : ι) : ℝ := ∑ T, ∑ a, if M.vert T a = i then M.ω T * M.m T else 0
def mu (i k : ι) : ℝ := ∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then M.ω T * M.m T else 0
def e (i k : ι) : Vec d := M.pos k - M.pos i
def volΩ : ℝ := ∑ T, M.ω T * M.vol T
/-- `β_i = ∫ ∇φ_i = Σ_T ω_T |T| g_i^T`. -/
def beta (i : ι) : Vec d := ∑ T, ∑ a, if M.vert T a = i then (M.ω T * M.vol T) • M.g T a else 0

/-- Interior vertex in the algebraic sense: the boundary mass matrix row of `i` vanishes. -/
def Closed (i : ι) : Prop := ∀ k, M.B i k = 0

/-- Edge projection `ν_ik = (n·e/|e|²) e`, and the geometric dissipation tensor of a choice `y`. -/
def nuOf (y e : Vec d) : Vec d := (dot y e / dot e e) • e
def nu (i k : ι) : Vec d := nuOf (M.n i k) (M.e i k)
def unit (v : Vec d) : Vec d := (1 / len v) • v
def Gtensor (y : ι → ι → Vec d) (i : ι) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ k, (len (y i k) * len (M.e i k)) • outer (unit (M.e i k)) (unit (M.e i k))

/-- Vertex set of the facet of `T` opposite local vertex `o`. -/
def facetNodes (p : C × Fin (d + 1)) : Finset ι := (Finset.univ.erase p.2).map (M.vert p.1)
def facetVec (p : C × Fin (d + 1)) : Vec d := (M.simplex p.1).facet p.2

/-- Facet pairing at `i`: the facets containing `i` are matched in pairs with the same vertex set, the same
weight and opposite area vectors (the interior vertex of a conforming mesh). -/
def FacetPaired (i : ι) : Prop :=
  ∃ σ : C × Fin (d + 1) → C × Fin (d + 1), ∀ p, i ∈ M.facetNodes p →
    σ (σ p) = p ∧ σ p ≠ p ∧ M.facetNodes (σ p) = M.facetNodes p ∧ M.ω (σ p).1 = M.ω p.1 ∧
      M.facetVec (σ p) = -M.facetVec p

/-- P1 gradient of nodal values on cell `T`: `Σ_a w_a ⊗ g_a` (rows: components, columns: directions). -/
def gradW {κ : Type} (w : ι → κ → ℝ) (T : C) : Matrix κ (Fin d) ℝ :=
  ∑ a, fun r α => w (M.vert T a) r * M.g T a α

/-- Galerkin residual `R_i = -Σ_{T∋i} ω_T |T| F_T g_i^T` of element fluxes `F_T`. -/
def galerkinRes {κ : Type} [Fintype κ] (Fl : C → Matrix κ (Fin d) ℝ) (i : ι) : κ → ℝ :=
  -∑ T, ∑ a, if M.vert T a = i then (M.ω T * M.vol T) • (Fl T).mulVec (M.g T a) else 0

/-- Finite-volume residual over dual facet vectors `S T i k` inside each cell. -/
def fvRes {κ : Type} [Fintype κ] (Fl : C → Matrix κ (Fin d) ℝ) (S : C → ι → ι → Vec d) (i : ι) : κ → ℝ :=
  ∑ T, ∑ a, ∑ b, if M.vert T a = i then M.ω T • (Fl T).mulVec (S T i (M.vert T b)) else 0

end WMesh

namespace WMesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

/-- Defect of a dual with weights `W` (paper eq. nE): `E_ik = Σ_{T∋i,k} ½[(W_i - m) g_k + (W_k - m) g_i]`. For
`i = k` this is the diagonal of `s`. -/
def EW (W : C → Fin (d + 1) → ℝ) (i k : ι) : Vec d :=
  ∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then
    (M.ω T / 2) • ((W T a - M.m T) • M.g T b + (W T b - M.m T) • M.g T a) else 0

end WMesh

end CFDLean.Num

namespace CFDLean.Num.Internal

section
variable {ι C X : Type} [Fintype ι] [DecidableEq ι] [Fintype C] [AddCommMonoid X] {d : ℕ}
  (M : WMesh ι C d)

/-- Summing over the second vertex index collapses the indicator. -/
theorem sum_second (i : ι) (f : C → Fin (d + 1) → Fin (d + 1) → X) :
    (∑ k, ∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then f T a b else 0) =
      ∑ T, ∑ a, ∑ b, if M.vert T a = i then f T a b else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases ha : M.vert T a = i
  · simp [ha]
  · simp [ha]

/-- Summing over the first vertex index collapses the indicator. -/
theorem sum_first (k : ι) (f : C → Fin (d + 1) → Fin (d + 1) → X) :
    (∑ i, ∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then f T a b else 0) =
      ∑ T, ∑ a, ∑ b, if M.vert T b = k then f T a b else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : M.vert T b = k
  · simp [hb]
  · simp [hb]

/-- Summing over the vertex of a single indicator. -/
theorem sum_single (f : C → Fin (d + 1) → X) :
    (∑ i, ∑ T, ∑ a, if M.vert T a = i then f T a else 0) = ∑ T, ∑ a, f T a := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp
end

/-- MC-N.P1-2.3 (JST `Paper1.Spec.P1_2_3`, proof `Paper1.Proofs.p1_2_3`). P1-2.3: the P1 operator of any dual has `Σ_k n_ik = -β_i`; at a closed vertex `β_i = 0`. -/
theorem _root_.CFDLean.Num.WMesh.nW_row_sum :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d)
      (W : C → Fin (d + 1) → ℝ), M.Valid → (∀ T, ∑ a, W T a = M.vol T) →
      (∀ i, ∑ k, M.nW W i k = -M.beta i) ∧ (∀ i, M.Closed i → M.beta i = 0) := by
  intro ι C _ _ _ d M W _hM hW
  have hrow : ∀ (W' : C → Fin (d + 1) → ℝ) i, ∑ k, M.cW W' i k = 0 := by
    intro W' i
    unfold WMesh.cW
    rw [sum_second M i (fun T a b => (M.ω T * W' T a) • M.g T b)]
    refine Finset.sum_eq_zero fun T _ => Finset.sum_eq_zero fun a _ => ?_
    split_ifs
    · rw [← Finset.smul_sum]
      simp only [WMesh.g]
      rw [grad_sum, smul_zero]
    · simp
  have hcol : ∀ (W' : C → Fin (d + 1) → ℝ), (∀ T, ∑ a, W' T a = M.vol T) →
      ∀ i, ∑ k, M.cW W' k i = M.beta i := by
    intro W' hW' i
    unfold WMesh.cW WMesh.beta
    rw [sum_first M i (fun T a b => (M.ω T * W' T a) • M.g T b)]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [← Finset.sum_smul, ← Finset.mul_sum, hW']
    · simp
  have hmed : ∀ T, ∑ a : Fin (d + 1), (fun T (_ : Fin (d + 1)) => M.m T) T a = M.vol T := by
    intro T
    simp only [WMesh.m, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  refine ⟨?_, ?_⟩
  · intro i
    unfold WMesh.nW
    rw [Finset.sum_sub_distrib, hrow, hcol W hW, zero_sub]
  · intro i hi
    have hB : ∑ k, M.B i k = 0 := Finset.sum_eq_zero fun k _ => hi k
    unfold WMesh.B WMesh.c at hB
    rw [Finset.sum_add_distrib, hrow, hcol _ hmed, zero_add] at hB
    exact hB

theorem pairF_sum' {κ ι : Type} [Fintype κ] (x : κ → ℝ) (s : Finset ι) (F : ι → κ → ℝ) :
    pairF x (∑ k ∈ s, F k) = ∑ k ∈ s, pairF x (F k) := by
  simp only [pairF, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem pairF_neg' {κ : Type} [Fintype κ] (x z : κ → ℝ) : pairF x (-z) = -pairF x z := by
  simp only [pairF, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem pairF_smul' {κ : Type} [Fintype κ] (x z : κ → ℝ) (c : ℝ) : pairF x (c • z) = c * pairF x z := by
  simp only [pairF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem pairF_mulVec {κ : Type} [Fintype κ] {d : ℕ} (w : κ → ℝ) (A : Matrix κ (Fin d) ℝ) (g : Vec d) :
    pairF w (A.mulVec g) = ∑ r, ∑ α, (w r * g α) * A r α := by
  simp only [pairF, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

namespace Closure
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

theorem facet_sum (T : Simplex d) : ∑ o, T.facet o = 0 := by
  simp only [Simplex.facet, ← Finset.smul_sum, grad_sum, smul_zero]

theorem mem_facetNodes (p : C × Fin (d + 1)) (i : ι) :
    i ∈ M.facetNodes p ↔ ∃ a, a ≠ p.2 ∧ M.vert p.1 a = i := by
  simp only [WMesh.facetNodes, Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true]

theorem vert_mem_facetNodes (T : C) (a o : Fin (d + 1)) :
    M.vert T a ∈ M.facetNodes (T, o) ↔ a ≠ o := by
  rw [mem_facetNodes]
  constructor
  · rintro ⟨b, hb, he⟩
    rwa [← (M.vert T).injective he]
  · intro h
    exact ⟨a, h, rfl⟩

theorem not_mem_facetNodes (T : C) (o : Fin (d + 1)) (i : ι) (hi : ∀ a, M.vert T a ≠ i) :
    i ∉ M.facetNodes (T, o) := by
  rw [mem_facetNodes]
  rintro ⟨a, -, ha⟩
  exact hi a ha

/-- Per-cell identity: `d (d+1) m_T (g_a + g_b)` is (1 or 2 times) the sum of the facet vectors of the facets
of `T` containing both `i = vert a` and `k = vert b`. -/
theorem cell_identity (T : C) (i k : ι) :
    ((d : ℝ) * ((d : ℝ) + 1)) • (∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then
        M.m T • (M.g T a + M.g T b) else 0) =
      (if i = k then (2 : ℝ) else 1) •
        ∑ o, if i ∈ M.facetNodes (T, o) ∧ k ∈ M.facetNodes (T, o) then M.facetVec (T, o) else 0 := by
  by_cases hi : ∃ a, M.vert T a = i
  swap
  · push Not at hi
    have h1 : ∀ a b, ¬ (M.vert T a = i ∧ M.vert T b = k) := fun a b h => hi a h.1
    have h2 : ∀ o, ¬ (i ∈ M.facetNodes (T, o) ∧ k ∈ M.facetNodes (T, o)) :=
      fun o h => not_mem_facetNodes M T o i hi h.1
    simp [h1, h2]
  by_cases hk : ∃ b, M.vert T b = k
  swap
  · push Not at hk
    have h1 : ∀ a b, ¬ (M.vert T a = i ∧ M.vert T b = k) := fun a b h => hk b h.2
    have h2 : ∀ o, ¬ (i ∈ M.facetNodes (T, o) ∧ k ∈ M.facetNodes (T, o)) :=
      fun o h => not_mem_facetNodes M T o k hk h.2
    simp [h1, h2]
  obtain ⟨a0, rfl⟩ := hi
  obtain ⟨b0, rfl⟩ := hk
  have hL : (∑ a, ∑ b, if M.vert T a = M.vert T a0 ∧ M.vert T b = M.vert T b0 then
        M.m T • (M.g T a + M.g T b) else 0) = M.m T • (M.g T a0 + M.g T b0) := by
    simp [(M.vert T).injective.eq_iff, ite_and]
  rw [hL]
  simp only [vert_mem_facetNodes, (M.vert T).injective.eq_iff]
  have hFs : ∑ o, M.facetVec (T, o) = 0 := by
    simp only [WMesh.facetVec]; exact facet_sum (M.simplex T)
  have hFo : ∀ o, M.facetVec (T, o) = (-((d : ℝ) * M.vol T)) • M.g T o := by
    intro o; simp only [WMesh.facetVec, Simplex.facet, WMesh.vol, WMesh.g]
  have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
  by_cases hab : a0 = b0
  · subst hab
    have e : ∀ o, (if a0 ≠ o ∧ a0 ≠ o then M.facetVec (T, o) else 0) =
        M.facetVec (T, o) - (if o = a0 then M.facetVec (T, o) else 0) := by
      intro o
      by_cases h : o = a0
      · subst h; simp
      · simp [h, Ne.symm h]
    simp only [e, Finset.sum_sub_distrib, hFs, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hFo]
    ext α
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul, WMesh.m]
    field_simp
    ring
  · have e : ∀ o, (if a0 ≠ o ∧ b0 ≠ o then M.facetVec (T, o) else 0) =
        M.facetVec (T, o) - (if o = a0 then M.facetVec (T, o) else 0) -
          (if o = b0 then M.facetVec (T, o) else 0) := by
      intro o
      by_cases h : o = a0
      · subst h; simp [hab]
      · by_cases h' : o = b0
        · subst h'; simp [h]
        · simp [h, h', Ne.symm h, Ne.symm h']
    simp only [e, Finset.sum_sub_distrib, hFs, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hab, ite_false]
    rw [hFo, hFo]
    ext α
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
      WMesh.m]
    field_simp
    ring

/-- `B_ik = Σ_T Σ_{a,b} [vert a = i, vert b = k] ω_T m_T (g_a + g_b)`. -/
theorem B_eq (i k : ι) : M.B i k = ∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then
    M.ω T • (M.m T • (M.g T a + M.g T b)) else 0 := by
  have h2 : M.c k i = ∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then
      (M.ω T * M.m T) • M.g T a else 0 := by
    unfold WMesh.c WMesh.cW
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h1 : M.vert T a = i <;> by_cases h2 : M.vert T b = k <;> simp [h1, h2]
  unfold WMesh.B
  rw [h2]
  unfold WMesh.c WMesh.cW
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rw [← smul_add, smul_smul]
    congr 1
    abel
  · simp

end Closure

namespace Sbp6

section Mesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

theorem cW_row (W : C → Fin (d + 1) → ℝ) (i : ι) : ∑ k, M.cW W i k = 0 := by
  unfold WMesh.cW
  rw [sum_second M i (fun T a b => (M.ω T * W T a) • M.g T b)]
  refine Finset.sum_eq_zero fun T _ => Finset.sum_eq_zero fun a _ => ?_
  split_ifs
  · rw [← Finset.smul_sum]
    simp only [WMesh.g]
    rw [grad_sum, smul_zero]
  · simp

theorem cW_col (W : C → Fin (d + 1) → ℝ) (hW : ∀ T, ∑ a, W T a = M.vol T) (k : ι) :
    ∑ i, M.cW W i k = M.beta k := by
  unfold WMesh.cW WMesh.beta
  rw [sum_first M k (fun T a b => (M.ω T * W T a) • M.g T b)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rw [← Finset.sum_smul, ← Finset.mul_sum, hW]
  · simp

theorem m_sum (T : C) : ∑ _a : Fin (d + 1), M.m T = M.vol T := by
  simp only [WMesh.m, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

theorem c_row (i : ι) : ∑ k, M.c i k = 0 := cW_row M _ i

theorem c_col (k : ι) : ∑ i, M.c i k = M.beta k := cW_col M _ (fun T => m_sum M T) k

theorem B_row (i : ι) : ∑ k, M.B i k = M.beta i := by
  unfold WMesh.B
  rw [Finset.sum_add_distrib, c_row, zero_add, c_col]

/-- Transposed operator as a sum over the same index pattern. -/
theorem cW_swap (W : C → Fin (d + 1) → ℝ) (i k : ι) : M.cW W k i = ∑ T, ∑ a, ∑ b,
    if M.vert T a = i ∧ M.vert T b = k then (M.ω T * W T b) • M.g T a else 0 := by
  unfold WMesh.cW
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : M.vert T a = i <;> by_cases h2 : M.vert T b = k <;> simp [h1, h2]

end Mesh

theorem mulVec_fsum {κ ι : Type} [Fintype κ] [Fintype ι] {d : ℕ} (A : Matrix κ (Fin d) ℝ) (v : ι → Vec d) :
    ∑ k, A.mulVec (v k) = A.mulVec (∑ k, v k) := by
  have := map_sum (Matrix.mulVecLin A) v Finset.univ
  simp only [Matrix.mulVecLin_apply] at this
  exact this.symm

end Sbp6

section
open Sbp6

/-- MC-N.P2-6.1 (JST `Paper1.Spec.P2_6_1`, proof `Paper1.Proofs.p2_6_1`). P2-6.1 (`prop:sbp`): for any dual with `Σ_a W_a^T = |T|`: `c + cᵀ = B_c + 2s` with `s` symmetric, zero row sums and entries `E_ik`; zero row sums of `c`, column sums `β`. -/
theorem _root_.CFDLean.Num.WMesh.sbp_defect :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d)
      (W : C → Fin (d + 1) → ℝ), (∀ T, ∑ a, W T a = M.vol T) →
      (∀ i k, M.cW W i k + M.cW W k i = M.B i k + (2 : ℝ) • M.EW W i k) ∧
      (∀ i k, M.EW W k i = M.EW W i k) ∧ (∀ i, ∑ k, M.EW W i k = 0) ∧
      (∀ i, ∑ k, M.cW W i k = 0) ∧ (∀ k, ∑ i, M.cW W i k = M.beta k) := by
  intro ι C _ _ _ d M W hW
  refine ⟨?_, ?_, ?_, cW_row M W, cW_col M W hW⟩
  · intro i k
    rw [cW_swap M W i k, Closure.B_eq]
    unfold WMesh.cW WMesh.EW
    rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · ext α
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp
  · intro i k
    unfold WMesh.EW
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [and_comm, add_comm]
  · intro i
    unfold WMesh.EW
    rw [sum_second M i (fun T a b =>
      (M.ω T / 2) • ((W T a - M.m T) • M.g T b + (W T b - M.m T) • M.g T a))]
    refine Finset.sum_eq_zero fun T _ => Finset.sum_eq_zero fun a _ => ?_
    split_ifs
    · rw [← Finset.smul_sum, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul]
      have hg : ∑ b, M.g T b = 0 := by simp only [WMesh.g]; exact grad_sum _
      have hs : ∑ b, (W T b - M.m T) = 0 := by rw [Finset.sum_sub_distrib, hW, m_sum]; ring
      rw [hg, hs, smul_zero, zero_smul, add_zero, smul_zero]
    · simp

/-- MC-N.P2-6.2 (JST `Paper1.Spec.P2_6_2`, proof `Paper1.Proofs.p2_6_2`). P2-6.2 (`prop:sbp` last sentence, `prop:defect` first sentence): on one nondegenerate simplex, with `δ_a = W_a - m_T` (`Σ δ = 0`), all off-diagonal defect terms vanish iff `W = m_T`. -/
theorem _root_.CFDLean.Num.Simplex.median_defect_iff :
    ∀ (d : ℕ) (T : Simplex d) (δ : Fin (d + 1) → ℝ), 1 ≤ d → T.Nondeg → ∑ a, δ a = 0 →
      ((∀ a b, a ≠ b → δ a • T.grad b + δ b • T.grad a = 0) ↔ ∀ a, δ a = 0) := by
  intro d T δ hd hT hsum
  have hc := Simplex.calculus d T hT
  constructor
  · intro h a
    have hz : ∑ b, (δ a • T.grad b + δ b • T.grad a) - (δ a • T.grad a + δ a • T.grad a) = 0 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a), add_sub_cancel_right]
      exact Finset.sum_eq_zero fun b hb => h a b (Finset.ne_of_mem_erase hb).symm
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul, hc.1, hsum, smul_zero, zero_smul,
      zero_add, zero_sub, neg_eq_zero, ← add_smul] at hz
    rcases smul_eq_zero.mp hz with h0 | h0
    · linarith
    · exfalso
      obtain ⟨c, hca⟩ : ∃ c : Fin (d + 1), c ≠ a := by
        have h0l : (0 : Fin (d + 1)) ≠ Fin.last d := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        by_cases ha : a = 0
        · exact ⟨Fin.last d, by rw [ha]; exact h0l.symm⟩
        · exact ⟨0, Ne.symm ha⟩
      have := hc.2.1 a a c
      rw [h0, ite_eq_left rfl, ite_eq_right (Ne.symm hca)] at this
      simp [dot] at this
  · intro h a b _
    simp [h]

end

namespace DissGeom

section Vec
variable {d : ℕ}

theorem dot_sum_left {β : Type} (s : Finset β) (f : β → Vec d) (v : Vec d) :
    dot (∑ j ∈ s, f j) v = ∑ j ∈ s, dot (f j) v := by
  simp only [dot, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem dot_ite_left (p : Prop) [Decidable p] (u v : Vec d) :
    dot (if p then u else 0) v = if p then dot u v else 0 := by
  split_ifs <;> simp [dot]

theorem dot_smul_l (c : ℝ) (u v : Vec d) : dot (c • u) v = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_smul_r (c : ℝ) (u v : Vec d) : dot u (c • v) = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_sub_l (u v w : Vec d) : dot (u - v) w = dot u w - dot v w := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dot_zero_r (u : Vec d) : dot u 0 = 0 := by simp [dot]

theorem dot_self_nonneg (u : Vec d) : 0 ≤ dot u u :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem eq_zero_of_dot_self (u : Vec d) (h : dot u u = 0) : u = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => mul_self_nonneg (u α))).1 h
  funext α
  exact mul_self_eq_zero.1 (this α (Finset.mem_univ _))

theorem len_nonneg (u : Vec d) : 0 ≤ len u := Real.sqrt_nonneg _

theorem len_mul_self (u : Vec d) : len u * len u = dot u u :=
  Real.mul_self_sqrt (dot_self_nonneg u)

theorem len_zero : len (0 : Vec d) = 0 := by simp [len, dot]

theorem len_smul' (c : ℝ) (u : Vec d) : len (c • u) = |c| * len u := by
  unfold len
  rw [dot_smul_l, dot_smul_r, ← mul_assoc, Real.sqrt_mul' _ (dot_self_nonneg u),
    Real.sqrt_mul_self_eq_abs]

theorem dot_unit (u : Vec d) :
    dot (WMesh.unit u) (WMesh.unit u) = if len u = 0 then 0 else 1 := by
  unfold WMesh.unit
  rw [dot_smul_l, dot_smul_r, ← len_mul_self]
  split_ifs with h
  · simp [h]
  · field_simp

theorem trace_outer (u v : Vec d) : Matrix.trace (outer u v) = dot u v := by
  simp [Matrix.trace, Matrix.diag, outer, dot]

theorem outer_sum_left {β : Type} (s : Finset β) (f : β → Vec d) (v : Vec d) :
    outer (∑ j ∈ s, f j) v = ∑ j ∈ s, outer (f j) v := by
  ext α γ
  simp [outer, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]

theorem outer_ite_left (p : Prop) [Decidable p] (u v : Vec d) :
    outer (if p then u else 0) v = if p then outer u v else 0 := by
  split_ifs
  · rfl
  · ext α γ; simp [outer]

theorem outer_smul_left (c : ℝ) (u v : Vec d) : outer (c • u) v = c • outer u v := by
  ext α γ; simp [outer, mul_assoc]

theorem outer_smul_right (c : ℝ) (u v : Vec d) : outer u (c • v) = c • outer u v := by
  ext α γ
  simp only [outer, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

theorem outer_sub_right (u v w : Vec d) : outer u (v - w) = outer u v - outer u w := by
  ext α γ; simp [outer, mul_sub]

theorem outer_sub_left (u v w : Vec d) : outer (u - v) w = outer u w - outer v w := by
  ext α γ; simp [outer, sub_mul]

theorem outer_neg_right (u v : Vec d) : outer u (-v) = -outer u v := by
  ext α γ; simp [outer]

theorem quad (y e : Vec d) (t : ℝ) :
    dot (y - t • e) (y - t • e) = dot y y - 2 * t * dot y e + t ^ 2 * dot e e := by
  simp only [dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Cauchy–Schwarz with its equality case. -/
theorem cs (y e : Vec d) (h : dot e e ≠ 0) : dot y e ^ 2 ≤ dot y y * dot e e ∧
    (dot y e ^ 2 = dot y y * dot e e → y = (dot y e / dot e e) • e) := by
  have hq := quad y e (dot y e / dot e e)
  have hq' : dot (y - (dot y e / dot e e) • e) (y - (dot y e / dot e e) • e) * dot e e =
      dot y y * dot e e - dot y e ^ 2 := by
    rw [hq]; field_simp; ring
  have hee : 0 < dot e e := lt_of_le_of_ne (dot_self_nonneg e) (Ne.symm h)
  constructor
  · have := mul_nonneg (dot_self_nonneg (y - (dot y e / dot e e) • e)) hee.le
    linarith
  · intro heq
    have h0 : dot (y - (dot y e / dot e e) • e) (y - (dot y e / dot e e) • e) = 0 := by
      have h1 : dot (y - (dot y e / dot e e) • e) (y - (dot y e / dot e e) • e) * dot e e = 0 := by
        rw [hq', heq, sub_self]
      exact (mul_eq_zero.1 h1).resolve_right h
    exact sub_eq_zero.1 (eq_zero_of_dot_self _ h0)

theorem dot_le_len (y e : Vec d) : dot y e ≤ len y * len e := by
  rcases eq_or_ne (dot e e) 0 with h | h
  · rw [eq_zero_of_dot_self e h, dot_zero_r]
    exact mul_nonneg (len_nonneg _) (len_nonneg _)
  · calc dot y e ≤ |dot y e| := le_abs_self _
      _ ≤ Real.sqrt (dot y y * dot e e) := Real.abs_le_sqrt (cs y e h).1
      _ = len y * len e := Real.sqrt_mul (dot_self_nonneg y) _

theorem term_ge (y e : Vec d) :
    dot y e ≤ len y * len e * dot (WMesh.unit e) (WMesh.unit e) := by
  rw [dot_unit]
  split_ifs with h
  · have h0 : dot e e = 0 := by rw [← len_mul_self, h, mul_zero]
    rw [eq_zero_of_dot_self e h0, dot_zero_r, mul_zero]
  · rw [mul_one]; exact dot_le_len y e

theorem term_eq_iff (y e : Vec d) (hy : e = 0 → y = 0) :
    len y * len e * dot (WMesh.unit e) (WMesh.unit e) = dot y e ↔
      ∃ t : ℝ, 0 ≤ t ∧ y = t • e := by
  rw [dot_unit]
  split_ifs with h
  · have he : e = 0 := eq_zero_of_dot_self e (by rw [← len_mul_self, h, mul_zero])
    have hy0 := hy he
    rw [he, dot_zero_r, mul_zero]
    simp only [true_iff]
    exact ⟨0, le_rfl, by rw [hy0, smul_zero]⟩
  · rw [mul_one]
    have hee : dot e e ≠ 0 := fun h0 => h (by rw [len, h0, Real.sqrt_zero])
    constructor
    · intro heq
      refine ⟨dot y e / dot e e, div_nonneg ?_ (dot_self_nonneg e), (cs y e hee).2 ?_⟩
      · rw [← heq]; exact mul_nonneg (len_nonneg _) (len_nonneg _)
      · rw [← heq, mul_pow, sq, sq, len_mul_self, len_mul_self]
    · rintro ⟨t, ht, rfl⟩
      rw [len_smul', abs_of_nonneg ht, dot_smul_l, ← len_mul_self]
      ring

end Vec

section Mesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

theorem gdot (hM : M.Valid) (T : C) (a b c : Fin (d + 1)) :
    dot (M.g T a) (M.pos (M.vert T b) - M.pos (M.vert T c)) =
      (if a = b then 1 else 0) - (if a = c then 1 else 0) :=
  (Simplex.calculus d (M.simplex T) (hM.2 T)).2.1 a b c

theorem m_pos (hM : M.Valid) (T : C) : 0 < M.m T :=
  div_pos (Simplex.calculus d (M.simplex T) (hM.2 T)).2.2.2.1 (by positivity)

theorem wm_nonneg (hM : M.Valid) (T : C) : 0 ≤ M.ω T * M.m T :=
  mul_nonneg (hM.1 T) (m_pos M hM T).le

theorem pos_ne (hM : M.Valid) (T : C) (a b : Fin (d + 1)) (hab : a ≠ b) :
    M.pos (M.vert T b) - M.pos (M.vert T a) ≠ 0 := by
  intro h
  have := gdot M hM T b b a
  rw [h, dot_zero_r, ite_eq_left rfl, ite_eq_right (Ne.symm hab)] at this
  norm_num at this

theorem e_self (i : ι) : M.e i i = 0 := sub_self _

theorem mu_nonneg (hM : M.Valid) (i k : ι) : 0 ≤ M.mu i k :=
  Finset.sum_nonneg fun T _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact wm_nonneg M hM T
    · exact le_rfl

theorem mu_symm (i k : ι) : M.mu k i = M.mu i k := by
  unfold WMesh.mu
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [and_comm]

theorem dot_c (i k : ι) (v : Vec d) :
    dot (M.c i k) v = ∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then
      M.ω T * M.m T * dot (M.g T b) v else 0 := by
  unfold WMesh.c WMesh.cW
  simp only [dot_sum_left, dot_ite_left, dot_smul_l]

theorem dot_c_e (hM : M.Valid) (i k : ι) (hik : i ≠ k) : dot (M.c i k) (M.e i k) = M.mu i k := by
  rw [dot_c]
  unfold WMesh.mu
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · obtain ⟨ha, hb⟩ := h
    have hab : b ≠ a := fun hba => hik (by subst hba; exact ha.symm.trans hb)
    unfold WMesh.e
    rw [← ha, ← hb, gdot M hM, ite_eq_left rfl, ite_eq_right hab]
    ring
  · rfl

theorem dot_c_e' (hM : M.Valid) (i k : ι) (hik : i ≠ k) :
    dot (M.c k i) (M.e i k) = -M.mu i k := by
  rw [dot_c, ← mu_symm M i k]
  unfold WMesh.mu
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · obtain ⟨ha, hb⟩ := h
    have hab : b ≠ a := fun hba => hik (by subst hba; exact hb.symm.trans ha)
    unfold WMesh.e
    rw [← ha, ← hb, gdot M hM, ite_eq_right hab, ite_eq_left rfl]
    ring
  · simp

theorem n_dot_e (hM : M.Valid) (i k : ι) (hik : i ≠ k) :
    dot (M.n i k) (M.e i k) = 2 * M.mu i k := by
  unfold WMesh.n
  rw [dot_sub_l, dot_c_e M hM i k hik, dot_c_e' M hM i k hik]
  ring

theorem cell_one (hM : M.Valid) (T : C) (a : Fin (d + 1)) :
    ∑ b, outer (M.g T b) (M.pos (M.vert T b) - M.pos (M.vert T a)) = 1 := by
  have h := Simplex.calculus d (M.simplex T) (hM.2 T)
  have h1 : ∑ b, M.g T b = 0 := h.1
  have h3 : ∑ b, outer (M.g T b) (M.pos (M.vert T b)) = 1 := h.2.2.1
  simp only [outer_sub_right, Finset.sum_sub_distrib]
  rw [← outer_sum_left, h1, h3]
  ext α γ
  simp [outer]

theorem c_outer_sum (hM : M.Valid) (i : ι) :
    ∑ k, outer (M.c i k) (M.e i k) = M.V i • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have step : ∀ k, outer (M.c i k) (M.e i k) = ∑ T, ∑ a, ∑ b,
      if M.vert T a = i ∧ M.vert T b = k then
        (M.ω T * M.m T) • outer (M.g T b) (M.pos (M.vert T b) - M.pos (M.vert T a)) else 0 := by
    intro k
    unfold WMesh.c WMesh.cW
    simp only [outer_sum_left, outer_ite_left, outer_smul_left]
    refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · obtain ⟨ha, hb⟩ := h
      unfold WMesh.e
      rw [ha, hb]
    · rfl
  simp only [step]
  rw [sum_second M i (fun T a b =>
    (M.ω T * M.m T) • outer (M.g T b) (M.pos (M.vert T b) - M.pos (M.vert T a)))]
  unfold WMesh.V
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [← Finset.smul_sum, cell_one M hM T a]
  · simp

theorem sum_V : ∑ i, M.V i = M.volΩ := by
  unfold WMesh.V WMesh.volΩ
  rw [sum_single (X := ℝ) M (fun T _ => M.ω T * M.m T)]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, WMesh.m]
  push_cast
  field_simp

theorem trace_G (y : ι → ι → Vec d) (i : ι) : Matrix.trace (M.Gtensor y i) =
    ∑ k, len (y i k) * len (M.e i k) * dot (WMesh.unit (M.e i k)) (WMesh.unit (M.e i k)) := by
  unfold WMesh.Gtensor
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, trace_outer, smul_eq_mul]

theorem e_zero_n_zero (hM : M.Valid) (i k : ι) (he : M.e i k = 0) : M.n i k = 0 := by
  by_cases hik : i = k
  · subst hik; exact sub_self _
  · have hc : ∀ i k, i ≠ k → M.pos k = M.pos i → M.c i k = 0 := by
      intro i k hik hp
      unfold WMesh.c WMesh.cW
      refine Finset.sum_eq_zero fun T _ => Finset.sum_eq_zero fun a _ =>
        Finset.sum_eq_zero fun b _ => ?_
      rw [ite_eq_right]
      rintro ⟨ha, hb⟩
      have hab : a ≠ b := fun h => hik (by subst h; exact ha.symm.trans hb)
      apply pos_ne M hM T a b hab
      rw [ha, hb, hp, sub_self]
    have hp : M.pos k = M.pos i := sub_eq_zero.1 (show M.pos k - M.pos i = 0 from he)
    unfold WMesh.n
    rw [hc i k hik hp, hc k i (Ne.symm hik) hp.symm, sub_self]

theorem nu_len_e (hM : M.Valid) (i k : ι) :
    len (M.nu i k) * len (M.e i k) = dot (M.n i k) (M.e i k) := by
  rcases eq_or_ne (dot (M.e i k) (M.e i k)) 0 with h | h
  · rw [eq_zero_of_dot_self _ h, dot_zero_r, len_zero, mul_zero]
  · have hik : i ≠ k := by
      rintro rfl; exact h (by rw [e_self, dot_zero_r])
    have hnn : 0 ≤ dot (M.n i k) (M.e i k) := by
      rw [n_dot_e M hM i k hik]; linarith [mu_nonneg M hM i k]
    unfold WMesh.nu WMesh.nuOf
    rw [len_smul', abs_of_nonneg (div_nonneg hnn (dot_self_nonneg _)), mul_assoc, len_mul_self]
    field_simp

theorem nu_term (hM : M.Valid) (i k : ι) :
    len (M.nu i k) * len (M.e i k) * dot (WMesh.unit (M.e i k)) (WMesh.unit (M.e i k)) =
      dot (M.n i k) (M.e i k) := by
  rw [dot_unit]
  split_ifs with h
  · have h0 : dot (M.e i k) (M.e i k) = 0 := by rw [← len_mul_self, h, mul_zero]
    rw [eq_zero_of_dot_self _ h0, dot_zero_r, mul_zero]
  · rw [mul_one, nu_len_e M hM]

end Mesh
end DissGeom

section
open DissGeom

/-- MC-N.P1-5.2 (JST `Paper1.Spec.P1_5_2`, proof `Paper1.Proofs.p1_5_2`). P1-5.2 (`lem:dissgeom`(a)): `n·e = 2μ > 0`, and `ν` is a positive multiple of `e` with `|ν| = n·e/|e|`. -/
theorem _root_.CFDLean.Num.WMesh.dissGeom_edge :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d), M.Valid →
      (∀ i k, i ≠ k → dot (M.n i k) (M.e i k) = 2 * M.mu i k) ∧
      (∀ i k, i ≠ k → (∃ T a b, M.vert T a = i ∧ M.vert T b = k ∧ 0 < M.ω T) →
        0 < M.mu i k ∧ (∃ t : ℝ, 0 < t ∧ M.nu i k = t • M.e i k) ∧
        len (M.nu i k) = dot (M.n i k) (M.e i k) / len (M.e i k)) := by
  intro ι C _ _ _ d M hM
  refine ⟨fun i k hik => n_dot_e M hM i k hik, ?_⟩
  rintro i k hik ⟨T, a, b, ha, hb, hω⟩
  have hab : a ≠ b := fun h => hik (by subst h; exact ha.symm.trans hb)
  have hnn : ∀ T a b, 0 ≤ (if M.vert T a = i ∧ M.vert T b = k then M.ω T * M.m T else 0) :=
    fun T a b => by
      split_ifs
      · exact wm_nonneg M hM T
      · exact le_rfl
  have hpos : 0 < (if M.vert T a = i ∧ M.vert T b = k then M.ω T * M.m T else 0) := by
    rw [ite_eq_left ⟨ha, hb⟩]; exact mul_pos hω (m_pos M hM T)
  have hmu : 0 < M.mu i k :=
    Finset.sum_pos' (fun T _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hnn T a b)
      ⟨T, Finset.mem_univ _, Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ => hnn T a b)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun b _ => hnn T a b) ⟨b, Finset.mem_univ _, hpos⟩⟩⟩
  have he : M.e i k ≠ 0 := by
    unfold WMesh.e; rw [← ha, ← hb]; exact pos_ne M hM T a b hab
  have hee : 0 < dot (M.e i k) (M.e i k) :=
    lt_of_le_of_ne (dot_self_nonneg _) (fun h => he (eq_zero_of_dot_self _ h.symm))
  have hne := n_dot_e M hM i k hik
  have hL : 0 < len (M.e i k) := Real.sqrt_pos.2 hee
  have ht : 0 < dot (M.n i k) (M.e i k) / dot (M.e i k) (M.e i k) :=
    div_pos (by rw [hne]; linarith) hee
  refine ⟨hmu, ⟨_, ht, rfl⟩, ?_⟩
  unfold WMesh.nu WMesh.nuOf
  rw [len_smul', abs_of_pos ht, ← len_mul_self (M.e i k)]
  field_simp

/-- MC-N.P1-5.3 (JST `Paper1.Spec.P1_5_3`, proof `Paper1.Proofs.p1_5_3`). P1-5.3 (`lem:dissgeom`(b)). -/
theorem _root_.CFDLean.Num.WMesh.dissGeom_outer :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d), M.Valid →
      (∀ i, ∑ k, outer (M.c i k) (M.e i k) = M.V i • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
      (∀ i, M.Closed i → ∑ k, outer (M.n i k) (M.e i k) = (2 * M.V i) • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
      (∑ i, ∑ k, outer (M.n i k) (M.e i k) = (2 * M.volΩ) • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
      (∑ i, M.V i = M.volΩ) := by
  intro ι C _ _ _ d M hM
  have h1 : ∑ i, ∑ k, outer (M.c i k) (M.e i k) = M.volΩ • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    simp only [c_outer_sum M hM]
    rw [← Finset.sum_smul, sum_V]
  have h2 : ∑ i, ∑ k, outer (M.c k i) (M.e i k) = -(M.volΩ • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    rw [Finset.sum_comm]
    have he : ∀ i k, M.e k i = -M.e i k := by intro i k; unfold WMesh.e; abel
    rw [← h1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [he, outer_neg_right]
  refine ⟨c_outer_sum M hM, ?_, ?_, sum_V M⟩
  · intro i hi
    have hn : ∀ k, M.n i k = (2 : ℝ) • M.c i k := by
      intro k
      have hB := hi k
      unfold WMesh.B at hB
      unfold WMesh.n
      rw [eq_neg_of_add_eq_zero_right hB, two_smul, sub_neg_eq_add]
    simp only [hn, outer_smul_left, ← Finset.smul_sum, c_outer_sum M hM i, smul_smul]
  · simp only [WMesh.n, outer_sub_left, Finset.sum_sub_distrib, h1, h2]
    rw [sub_neg_eq_add, ← add_smul]
    congr 1
    ring

/-- MC-N.P1-5.4 (JST `Paper1.Spec.P1_5_4`, proof `Paper1.Proofs.p1_5_4`). P1-5.4 (`lem:dissgeom`(c), calibration). Sums over ordered pairs; each pair counts twice. -/
theorem _root_.CFDLean.Num.WMesh.dissGeom_calibration :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d), M.Valid →
      (∀ i, M.Closed i → Matrix.trace (M.Gtensor M.nu i) = 2 * d * M.V i) ∧
      (∑ i, ∑ k, len (M.nu i k) * len (M.e i k) = 2 * d * M.volΩ) ∧
      (∀ i, M.Closed i → 2 * d * M.V i ≤ Matrix.trace (M.Gtensor M.n i)) ∧
      (∀ i, M.Closed i → (Matrix.trace (M.Gtensor M.n i) = 2 * d * M.V i ↔
        ∀ k, ∃ t : ℝ, 0 ≤ t ∧ M.n i k = t • M.e i k)) := by
  intro ι C _ _ _ d M hM
  have hcl : ∀ i, M.Closed i → ∑ k, dot (M.n i k) (M.e i k) = 2 * d * M.V i := by
    intro i hi
    have := congrArg Matrix.trace ((WMesh.dissGeom_outer ι C d M hM).2.1 i hi)
    rw [Matrix.trace_sum] at this
    simp only [trace_outer, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul] at this
    rw [this]; ring
  have hgl : ∑ i, ∑ k, dot (M.n i k) (M.e i k) = 2 * d * M.volΩ := by
    have := congrArg Matrix.trace (WMesh.dissGeom_outer ι C d M hM).2.2.1
    simp only [Matrix.trace_sum, trace_outer, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul] at this
    rw [this]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [trace_G, ← hcl i hi]
    exact Finset.sum_congr rfl fun k _ => nu_term M hM i k
  · rw [← hgl]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => nu_len_e M hM i k
  · intro i hi
    rw [trace_G, ← hcl i hi]
    exact Finset.sum_le_sum fun k _ => term_ge _ _
  · intro i hi
    have hle : ∀ k ∈ (Finset.univ : Finset ι), dot (M.n i k) (M.e i k) ≤
        len (M.n i k) * len (M.e i k) * dot (WMesh.unit (M.e i k)) (WMesh.unit (M.e i k)) :=
      fun k _ => term_ge _ _
    rw [trace_G, ← hcl i hi]
    constructor
    · intro h k
      exact (term_eq_iff _ _ (e_zero_n_zero M hM i k)).1
        ((Finset.sum_eq_sum_iff_of_le hle).1 h.symm k (Finset.mem_univ _)).symm
    · intro h
      exact ((Finset.sum_eq_sum_iff_of_le hle).2 fun k _ =>
        ((term_eq_iff _ _ (e_zero_n_zero M hM i k)).2 (h k)).symm).symm

end

namespace Dg7
open DissGeom

section Vec
variable {d : ℕ}

theorem dot_comm' (u v : Vec d) : dot u v = dot v u := by
  simp only [dot]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem bf_symm (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.IsSymm) (u v : Vec d) :
    dot u (H.mulVec v) = dot v (H.mulVec u) := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [hH.apply β α]
  ring

theorem dot_add_l (u v w : Vec d) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_add_r (u v w : Vec d) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem frob_outer (e : Vec d) (H : Matrix (Fin d) (Fin d) ℝ) :
    frob (outer e e) H = dot e (H.mulVec e) := by
  simp only [frob, outer, dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem frob_add (A B H : Matrix (Fin d) (Fin d) ℝ) : frob (A + B) H = frob A H + frob B H := by
  simp only [frob, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem frob_smul (c : ℝ) (A H : Matrix (Fin d) (Fin d) ℝ) : frob (c • A) H = c * frob A H := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem frob_sum {ι : Type} [Fintype ι] (A : ι → Matrix (Fin d) (Fin d) ℝ) (H : Matrix (Fin d) (Fin d) ℝ) :
    frob (∑ k, A k) H = ∑ k, frob (A k) H := by
  simp only [frob, Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem outer_psd (c : ℝ) (hc : 0 ≤ c) (e : Vec d) : (c • outer e e).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨Matrix.IsHermitian.ext fun α β => ?_, fun x => ?_⟩
  · simp [outer, mul_comm]
  · have h : dotProduct (star x) ((c • outer e e).mulVec x) =
        c * ((∑ α, x α * e α) * (∑ β, x β * e β)) := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, outer, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      ring
    rw [h]
    exact mul_nonneg hc (mul_self_nonneg _)

theorem psd_sum {ι : Type} [Fintype ι] (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (e : ι → Vec d) :
    (∑ k, c k • outer (e k) (e k)).PosSemidef := by
  classical
  have key : ∀ s : Finset ι, (∑ k ∈ s, c k • outer (e k) (e k)).PosSemidef := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty]
      exact Matrix.PosSemidef.zero
    · intro k s hk hs
      rw [Finset.sum_insert hk]
      exact (outer_psd _ (hc k) _).add hs
  exact key Finset.univ

theorem len_nuOf (y e : Vec d) (h : 0 < dot y e) :
    len (WMesh.nuOf y e) = dot y e / len e := by
  have hee : dot e e ≠ 0 := by
    intro h0; rw [eq_zero_of_dot_self e h0, dot_zero_r] at h; exact lt_irrefl _ h
  have hle : 0 < len e := Real.sqrt_pos.2 (lt_of_le_of_ne (dot_self_nonneg e) (Ne.symm hee))
  unfold WMesh.nuOf
  rw [len_smul', abs_of_nonneg (div_nonneg h.le (dot_self_nonneg e)), ← len_mul_self]
  field_simp

end Vec

section Mesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

theorem mu_self (i : ι) : M.mu i i = M.V i := by
  unfold WMesh.mu WMesh.V
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : M.vert T a = i
  · rw [ite_eq_left ha]
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      rw [ite_eq_right]
      rintro ⟨-, h⟩
      exact hb ((M.vert T).injective (h.trans ha.symm))
    · simp
  · rw [ite_eq_right ha]
    exact Finset.sum_eq_zero fun b _ => ite_eq_right fun h => ha h.1

theorem mu_row (i : ι) : ∑ k, M.mu i k = ((d : ℝ) + 1) * M.V i := by
  unfold WMesh.mu
  rw [sum_second M i (fun T _ _ => M.ω T * M.m T)]
  unfold WMesh.V
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  · simp

theorem ne_row (hM : M.Valid) (i : ι) : ∑ k, dot (M.n i k) (M.e i k) = 2 * d * M.V i := by
  have e : ∀ k, dot (M.n i k) (M.e i k) = 2 * M.mu i k - (if k = i then 2 * M.V i else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk; rw [e_self, dot_zero_r, ite_eq_left rfl, mu_self]; ring
    · rw [n_dot_e M hM i k (Ne.symm hk), ite_eq_right hk]; ring
  rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_sub_distrib, ← Finset.mul_sum, mu_row,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  ring

theorem ne_nonneg (hM : M.Valid) (i k : ι) : 0 ≤ dot (M.n i k) (M.e i k) := by
  by_cases hk : i = k
  · subst hk; rw [e_self, dot_zero_r]
  · rw [n_dot_e M hM i k hk]; linarith [mu_nonneg M hM i k]

/-- `|ν| |e|² = (n·e) |e|`. -/
theorem nu_ee (hM : M.Valid) (i k : ι) :
    len (M.nu i k) * dot (M.e i k) (M.e i k) = dot (M.n i k) (M.e i k) * len (M.e i k) := by
  rw [← len_mul_self (M.e i k), ← mul_assoc, nu_len_e M hM]

end Mesh
end Dg7

section
open Dg7 DissGeom

/-- MC-N.P2-7.1 (JST `Paper1.Spec.P2_7_1`, proof `Paper1.Proofs.p2_7_1`). P2-7.1: for quadratic `q` and any coefficients, `½ Σ_k λ_k (q_k - q_i)` is the first-order part plus `V K : ∇²q` with `K = (1/(4V)) Σ_k λ_k e_k ⊗ e_k`. -/
theorem _root_.CFDLean.Num.quadratic_edge_expansion :
    ∀ (ι : Type) [Fintype ι] (d : ℕ) (x : ι → Vec d) (i : ι) (lam : ι → ℝ) (V q0 : ℝ) (gq : Vec d)
      (H : Matrix (Fin d) (Fin d) ℝ), V ≠ 0 → H.IsSymm →
      let q : Vec d → ℝ := fun z => q0 + dot gq z + (1 / 2) * dot z (H.mulVec z)
      let K : Matrix (Fin d) (Fin d) ℝ := (1 / (4 * V)) • ∑ k, lam k • outer (x k - x i) (x k - x i)
      (1 / 2) * ∑ k, lam k * (q (x k) - q (x i)) =
        (1 / 2) * (∑ k, lam k * dot (gq + H.mulVec (x i)) (x k - x i)) + V * frob K H := by
  intro ι _ d x i lam V q0 gq H hV hH
  dsimp only
  have per : ∀ k, (q0 + dot gq (x k) + 1 / 2 * dot (x k) (H.mulVec (x k))) -
      (q0 + dot gq (x i) + 1 / 2 * dot (x i) (H.mulVec (x i))) =
      dot (gq + H.mulVec (x i)) (x k - x i) + 1 / 2 * dot (x k - x i) (H.mulVec (x k - x i)) := by
    intro k
    have hxk : x k = x i + (x k - x i) := by abel
    set e := x k - x i
    rw [hxk]
    simp only [Matrix.mulVec_add, dot_add_l, dot_add_r]
    rw [bf_symm H hH (x i) e, dot_comm' (H.mulVec (x i)) e]
    ring
  simp only [per]
  rw [frob_smul, frob_sum]
  simp only [frob_smul, frob_outer]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  ring

/-- MC-N.P2-7.2 (JST `Paper1.Spec.P2_7_2`, proof `Paper1.Proofs.p2_7_2`). P2-7.2: with `λ_k = σ_k |y_k|`: `|y| = |ν(y)| sec ϑ`, `sec ϑ ≥ 1`; `K(y) ⪰ K(ν)` in the Loewner order, with equality iff `y_k ∥ e_k` on every pair with `σ_k > 0`. -/
theorem _root_.CFDLean.Num.dissTensor_loewner :
    ∀ (ι : Type) [Fintype ι] (d : ℕ) (e y : ι → Vec d) (σ : ι → ℝ) (V : ℝ),
      0 < V → (∀ k, 0 ≤ σ k) → (∀ k, 0 < dot (y k) (e k)) →
      let K : (ι → Vec d) → Matrix (Fin d) (Fin d) ℝ :=
        fun z => (1 / (4 * V)) • ∑ k, (σ k * len (z k)) • outer (e k) (e k)
      let ν : ι → Vec d := fun k => WMesh.nuOf (y k) (e k)
      (∀ k, len (y k) = len (ν k) * (len (y k) * len (e k) / dot (y k) (e k)) ∧
        1 ≤ len (y k) * len (e k) / dot (y k) (e k)) ∧
      (K y - K ν).PosSemidef ∧
      (K y = K ν ↔ ∀ k, 0 < σ k → ∃ t : ℝ, 0 < t ∧ y k = t • e k) := by
  intro ι _ d e y σ V hV hσ hy
  dsimp only
  have hlen : ∀ k, len (WMesh.nuOf (y k) (e k)) ≤ len (y k) := by
    intro k
    rw [len_nuOf _ _ (hy k)]
    have hle : 0 < len (e k) := by
      have := dot_le_len (y k) (e k)
      by_contra h
      push Not at h
      have h0 : len (e k) = 0 := le_antisymm h (len_nonneg _)
      rw [h0, mul_zero] at this
      linarith [hy k]
    rw [div_le_iff₀ hle]
    exact dot_le_len _ _
  have hdiff : (1 / (4 * V)) • (∑ k, (σ k * len (y k)) • outer (e k) (e k)) -
      (1 / (4 * V)) • (∑ k, (σ k * len (WMesh.nuOf (y k) (e k))) • outer (e k) (e k)) =
      ∑ k, ((1 / (4 * V)) * (σ k * (len (y k) - len (WMesh.nuOf (y k) (e k))))) • outer (e k) (e k) := by
    rw [← smul_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_smul, smul_smul]
    congr 1
    ring
  have hc : ∀ k, 0 ≤ (1 / (4 * V)) * (σ k * (len (y k) - len (WMesh.nuOf (y k) (e k)))) := fun k =>
    mul_nonneg (by positivity) (mul_nonneg (hσ k) (sub_nonneg.2 (hlen k)))
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hle : 0 < len (e k) := by
      have := dot_le_len (y k) (e k)
      by_contra h
      push Not at h
      have h0 : len (e k) = 0 := le_antisymm h (len_nonneg _)
      rw [h0, mul_zero] at this
      linarith [hy k]
    refine ⟨?_, ?_⟩
    · rw [len_nuOf _ _ (hy k)]
      have := (hy k).ne'
      field_simp
    · rw [le_div_iff₀ (hy k), one_mul]
      exact dot_le_len _ _
  · rw [hdiff]
    exact psd_sum _ hc e
  · rw [← sub_eq_zero, hdiff]
    constructor
    · intro h k hk
      have htr := congrArg Matrix.trace h
      simp only [Matrix.trace_sum, Matrix.trace_smul, trace_outer, smul_eq_mul, Matrix.trace_zero] at htr
      have hterm : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤
          (1 / (4 * V)) * (σ j * (len (y j) - len (WMesh.nuOf (y j) (e j)))) * dot (e j) (e j) :=
        fun j _ => mul_nonneg (hc j) (dot_self_nonneg _)
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 htr k (Finset.mem_univ _)
      have hee : dot (e k) (e k) ≠ 0 := by
        intro h0; have := hy k; rw [eq_zero_of_dot_self _ h0, dot_zero_r] at this
        exact lt_irrefl _ this
      have hl : len (y k) = len (WMesh.nuOf (y k) (e k)) := by
        rcases mul_eq_zero.1 h0 with h1 | h1
        · rcases mul_eq_zero.1 h1 with h2 | h2
          · exfalso; have : (0 : ℝ) < 1 / (4 * V) := by positivity
            linarith
          · rcases mul_eq_zero.1 h2 with h3 | h3
            · linarith
            · linarith
        · exact absurd h1 hee
      rw [len_nuOf _ _ (hy k)] at hl
      have hle : 0 < len (e k) := Real.sqrt_pos.2 (lt_of_le_of_ne (dot_self_nonneg _) (Ne.symm hee))
      have hcs : dot (y k) (e k) ^ 2 = dot (y k) (y k) * dot (e k) (e k) := by
        rw [← len_mul_self (y k), ← len_mul_self (e k), hl]
        field_simp
      refine ⟨dot (y k) (e k) / dot (e k) (e k), div_pos (hy k) ?_, (cs _ _ hee).2 hcs⟩
      exact lt_of_le_of_ne (dot_self_nonneg _) (Ne.symm hee)
    · intro h
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases (hσ k).lt_or_eq with hk | hk
      · obtain ⟨t, ht, hyk⟩ := h k hk
        have hee : dot (e k) (e k) ≠ 0 := by
          intro h0; have := hy k; rw [eq_zero_of_dot_self _ h0, dot_zero_r] at this
          exact lt_irrefl _ this
        have : len (y k) = len (WMesh.nuOf (y k) (e k)) := by
          congr 1
          rw [hyk]
          unfold WMesh.nuOf
          rw [dot_smul_l]
          congr 1
          field_simp
        rw [this, sub_self, mul_zero, mul_zero, zero_smul]
      · rw [← hk, zero_mul, mul_zero, zero_smul]

/-- MC-N.P2-7.3 (JST `Paper1.Spec.P2_7_3`, proof `Paper1.Proofs.p2_7_3`). P2-7.3: `K_i = s G_i(y)/(4V_i)` if `σ_ik |e_ik| = s`; `tr K_i(ν) = d s/2` (at every vertex); and `tr K_i(ν) ≤ (d/2) σ_max h_i`. -/
theorem _root_.CFDLean.Num.WMesh.dissTensor_trace :
    ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d) (σ : ι → ι → ℝ)
      (s σmax h : ℝ) (y : ι → ι → Vec d) (i : ι), M.Valid → 0 < M.V i →
      let K : (ι → ι → Vec d) → Matrix (Fin d) (Fin d) ℝ :=
        fun z => (1 / (4 * M.V i)) • ∑ k, (σ i k * len (z i k)) • outer (M.e i k) (M.e i k)
      ((∀ k, k ≠ i → σ i k * len (M.e i k) = s) → K y = (s / (4 * M.V i)) • M.Gtensor y i) ∧
      ((∀ k, k ≠ i → σ i k * len (M.e i k) = s) → Matrix.trace (K M.nu) = d * s / 2) ∧
      ((∀ k, 0 ≤ σ i k ∧ σ i k ≤ σmax) → (∀ k, M.n i k ≠ 0 → len (M.e i k) ≤ h) →
        Matrix.trace (K M.nu) ≤ d / 2 * σmax * h) := by
  intro ι C _ _ _ d M σ s σmax h y i hM hV
  dsimp only
  have htrK : Matrix.trace ((1 / (4 * M.V i)) • ∑ k, (σ i k * len (M.nu i k)) • outer (M.e i k) (M.e i k)) =
      (1 / (4 * M.V i)) * ∑ k, σ i k * (dot (M.n i k) (M.e i k) * len (M.e i k)) := by
    simp only [Matrix.trace_smul, Matrix.trace_sum, trace_outer, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, nu_ee M hM]
  refine ⟨?_, ?_, ?_⟩
  · intro hs
    unfold WMesh.Gtensor
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, smul_smul]
    by_cases he : M.e i k = 0
    · rw [he]; ext α β; simp [outer, WMesh.unit]
    · have hle : 0 < len (M.e i k) := by
        refine Real.sqrt_pos.2 (lt_of_le_of_ne (dot_self_nonneg _) ?_)
        exact fun h0 => he (eq_zero_of_dot_self _ h0.symm)
      have hki : k ≠ i := by rintro rfl; exact he (e_self M k)
      have hσ : σ i k = s / len (M.e i k) := by
        rw [← hs k hki]; field_simp
      unfold WMesh.unit
      rw [outer_smul_left, outer_smul_right, smul_smul, smul_smul, hσ]
      congr 1
      field_simp
  · intro hs
    rw [htrK]
    have e : ∀ k, σ i k * (dot (M.n i k) (M.e i k) * len (M.e i k)) = s * dot (M.n i k) (M.e i k) := by
      intro k
      by_cases hki : k = i
      · subst hki; rw [e_self, dot_zero_r]; ring
      · rw [← hs k hki]; ring
    rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.mul_sum, ne_row M hM]
    field_simp
    ring
  · intro hσ hh
    rw [htrK]
    have hle : ∀ k, σ i k * (dot (M.n i k) (M.e i k) * len (M.e i k)) ≤ σmax * h * dot (M.n i k) (M.e i k) := by
      intro k
      by_cases hn : M.n i k = 0
      · rw [hn]; simp [dot]
      · have h1 := hh k hn
        have h2 := ne_nonneg M hM i k
        have h3 := len_nonneg (M.e i k)
        have h4 := (hσ k).1
        have h5 := (hσ k).2
        calc σ i k * (dot (M.n i k) (M.e i k) * len (M.e i k))
            ≤ σmax * (dot (M.n i k) (M.e i k) * len (M.e i k)) :=
              mul_le_mul_of_nonneg_right h5 (mul_nonneg h2 h3)
          _ ≤ σmax * (dot (M.n i k) (M.e i k) * h) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h2) (h4.trans h5)
          _ = σmax * h * dot (M.n i k) (M.e i k) := by ring
    calc (1 / (4 * M.V i)) * ∑ k, σ i k * (dot (M.n i k) (M.e i k) * len (M.e i k))
        ≤ (1 / (4 * M.V i)) * ∑ k, σmax * h * dot (M.n i k) (M.e i k) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hle k) (by positivity)
      _ = d / 2 * σmax * h := by
          rw [← Finset.mul_sum, ne_row M hM]
          field_simp
          ring

end

end CFDLean.Num.Internal
