import Paper1.Spec.Item14
import Paper1.Proofs.GeomBase
import Paper1.Proofs.Simplex
import Paper1.Proofs.Item6
import Paper1.Proofs.Item8
import Paper1.Proofs.Addendum2
import Paper1.Proofs.Item9

/-! Reviewer's non-vacuity check for `SchemeHyp` (P3 stage 2, not part of the build): on the P2 diamond mesh with
Simpson points on the outer edges, `SchemeHyp` holds for EVERY admissible nodal state field `u`, with the projected
states from P2-8.0/P2-8.0b. The diamond and the Simpson rule are copied from `reviews/P2/NonVacuity.lean`.
Compile with `lake env lean reviews/P3/SchemeHypNonVacuity.lean`. -/
noncomputable section
open scoped BigOperators
open NumCore Paper1

namespace ReviewP3

theorem grad_eq {d : ℕ} (T : Simplex d) (h : T.Nondeg) (a : Fin (d + 1)) (u : Vec d)
    (hu : ∀ b, dot u (T.x b - T.x 0) = (if a = b then 1 else 0) - (if a = 0 then 1 else 0)) :
    T.grad a = u := by
  apply Paper1.Proofs.vec_eq_of_dots T h
  intro b
  obtain ⟨-, hd, -⟩ := Paper1.Proofs.p1_5_1 d T h
  rw [hd a b 0, hu b]

/-! ### 1. The diamond: four right triangles around the origin. Vertex 4 is the centre. -/

def P : Fin 5 → Vec 2 := ![![1, 0], ![0, 1], ![-1, 0], ![0, -1], ![0, 0]]

def v0 : Fin 3 ↪ Fin 5 := ⟨fun a => ![4, 0, 1] a, by decide⟩
def v1 : Fin 3 ↪ Fin 5 := ⟨fun a => ![4, 1, 2] a, by decide⟩
def v2 : Fin 3 ↪ Fin 5 := ⟨fun a => ![4, 2, 3] a, by decide⟩
def v3 : Fin 3 ↪ Fin 5 := ⟨fun a => ![4, 3, 0] a, by decide⟩

def vt : Fin 4 → Fin 3 ↪ Fin 5 := ![v0, v1, v2, v3]

def diamond : WMesh (Fin 5) (Fin 4) 2 where
  pos := P
  vert := vt
  ω := fun _ => 1

def gv : Fin 4 → Fin 3 → Vec 2 :=
  ![![![-1, -1], ![1, 0], ![0, 1]],
    ![![1, -1], ![0, 1], ![-1, 0]],
    ![![1, 1], ![-1, 0], ![0, -1]],
    ![![-1, 1], ![0, -1], ![1, 0]]]

theorem diamond_nondeg (T : Fin 4) : (diamond.simplex T).Nondeg := by
  fin_cases T <;>
    simp [Simplex.Nondeg, Simplex.edgeMat, WMesh.simplex, diamond, Matrix.det_fin_two, vt, v0, v1, v2, v3, P]

theorem diamond_valid : diamond.Valid := ⟨fun _ => by simp [diamond], diamond_nondeg⟩

theorem diamond_g (T : Fin 4) (a : Fin 3) : diamond.g T a = gv T a := by
  unfold WMesh.g
  apply grad_eq _ (diamond_nondeg T)
  intro b
  fin_cases T <;> fin_cases a <;> fin_cases b <;>
    simp [dot, Fin.sum_univ_two, WMesh.simplex, diamond, vt, v0, v1, v2, v3, P, gv]

theorem diamond_vol (T : Fin 4) : diamond.vol T = 1 / 2 := by
  fin_cases T <;>
    simp [WMesh.vol, Simplex.vol, Simplex.edgeMat, WMesh.simplex, diamond, Matrix.det_fin_two, vt, v0, v1, v2,
      v3, P]

theorem diamond_facetVec (T : Fin 4) (o : Fin 3) : diamond.facetVec (T, o) = -(gv T o) := by
  have h1 : (diamond.simplex T).grad o = gv T o := diamond_g T o
  have h2 : (diamond.simplex T).vol = 1 / 2 := diamond_vol T
  simp only [WMesh.facetVec, Simplex.facet, h1, h2]
  funext x; simp

/-! ### 2. The diamond is conforming with the four outer edges (local facet 0) as boundary facets. -/

def bd : Fin 4 × Fin 3 → Bool := fun p => decide (p.2 = 0)

/-- Pairing of the interior edges: `(T,1) ↔ (T+1,2)`. -/
def sig : Fin 4 × Fin 3 → Fin 4 × Fin 3 := fun p =>
  if p.2 = 0 then p else if p.2 = 1 then (p.1 + 1, 2) else (p.1 - 1, 1)

theorem diamond_conforming : diamond.Conforming bd := by
  refine ⟨sig, ?_⟩
  intro p hp
  fin_cases p <;> simp [bd] at hp <;>
    refine ⟨by decide, by decide, by decide, by decide, rfl, ?_⟩ <;>
    simp only [sig] <;> norm_num <;>
    (rw [diamond_facetVec, diamond_facetVec]; funext x; fin_cases x <;> simp [gv])

/-- The centre is on no boundary facet. -/
theorem centre_off_boundary : ∀ p, bd p = true → (4 : Fin 5) ∉ diamond.facetNodes p := by
  intro p hp
  fin_cases p <;> simp [bd] at hp <;> decide


/-! ### 3. A face rule with (H1), (H2) on the diamond (P2-8.4): Simpson's rule on every outer edge.
Points `j = 0, 1, 2` at barycentric `(1,0), (1/2,1/2), (0,1)`, relative weights `1/6, 2/3, 1/6`. -/

def na : Fin 4 → Fin 5 := ![0, 1, 2, 3]
def nb : Fin 4 → Fin 5 := ![1, 2, 3, 0]

def fq : Fin 4 × Fin 3 → Fin 4 × Fin 3 := fun q => (q.1, 0)
def aq : Fin 4 × Fin 3 → ℝ := fun q => ![1 / 6, 2 / 3, 1 / 6] q.2
def phq : Fin 4 × Fin 3 → Fin 5 → ℝ := fun q k =>
  if k = na q.1 then ![1, 1 / 2, 0] q.2 else if k = nb q.1 then ![0, 1 / 2, 1] q.2 else 0

theorem fq_bd : ∀ q, bd (fq q) = true := by intro q; simp [bd, fq]

theorem phq_supp : ∀ q k, k ∉ diamond.facetNodes (fq q) → phq q k = 0 := by
  intro q k hk
  fin_cases q <;> fin_cases k <;> simp [phq, na, nb] <;> revert hk <;> decide

theorem simpson_H1 : ∀ p, bd p = true → ∀ i ∈ diamond.facetNodes p,
    (∑ q, if fq q = p then aq q * phq q i else 0) = 1 / ((2 : ℕ) : ℝ) := by
  intro p hp i hi
  fin_cases p <;> simp [bd] at hp <;> fin_cases i <;> revert hi <;> (try decide) <;> intro _ <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_succ, fq, aq, phq, na, nb] <;> norm_num

theorem sum_red (T : Fin 4) (f : Fin 4 × Fin 3 → ℝ) :
    (∑ q, if fq q = (T, 0) then f q else 0) = ∑ j, f (T, j) := by
  rw [Fintype.sum_prod_type]
  simp only [fq, Prod.mk.injEq, and_true]
  rw [Finset.sum_eq_single T (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem mem_nodes (T : Fin 4) (i : Fin 5) : i ∈ diamond.facetNodes (T, 0) → i = na T ∨ i = nb T := by
  fin_cases T <;> fin_cases i <;> decide

theorem na_ne_nb (T : Fin 4) : nb T ≠ na T := by fin_cases T <;> decide

theorem phq_a (T : Fin 4) (j : Fin 3) : phq (T, j) (na T) = ![1, 1 / 2, 0] j := by simp [phq]
theorem phq_b (T : Fin 4) (j : Fin 3) : phq (T, j) (nb T) = ![0, 1 / 2, 1] j := by
  simp [phq, na_ne_nb T]

theorem vec3_two (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl

theorem simpson_H2 : ∀ p, bd p = true → ∀ i ∈ diamond.facetNodes p, ∀ k ∈ diamond.facetNodes p,
    (∑ q, if fq q = p then aq q * phq q i * phq q k else 0) =
      (1 + if i = k then 1 else 0) / (((2 : ℕ) : ℝ) * ((2 : ℕ) + 1)) := by
  rintro ⟨T, o⟩ hp i hi k hk
  have ho : o = 0 := by simpa [bd] using hp
  subst ho
  rw [sum_red T (fun q => aq q * phq q i * phq q k)]
  rcases mem_nodes T i hi with rfl | rfl <;> rcases mem_nodes T k hk with rfl | rfl <;>
    simp only [phq_a, phq_b, Fin.sum_univ_succ, Fin.sum_univ_zero, aq, if_pos rfl, if_neg (na_ne_nb T),
      if_neg (Ne.symm (na_ne_nb T))] <;> norm_num [vec3_two]

/-! ### Conforming ⇒ facet balanced (the first part of P3-11.1, re-proved here: `Proofs/Item11a` is not built). -/

theorem balanced_of_conforming {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)
    (bd : C × Fin (d + 1) → Bool) (h : M.Conforming bd) : M.FacetBalanced bd := by
  obtain ⟨σ, hσ⟩ := h
  intro S
  let g : C × Fin (d + 1) → C × Fin (d + 1) := fun p => if bd p = false then σ p else p
  refine Finset.sum_ninvolution g ?_ ?_ (fun _ => Finset.mem_univ _) ?_
  · intro p
    by_cases hp : bd p = false
    · obtain ⟨-, -, h3, h4, h5, h6⟩ := hσ p hp
      have hg : g p = σ p := if_pos hp
      rw [hg]
      by_cases hS : M.facetNodes p = S
      · rw [if_pos ⟨hp, hS⟩, if_pos ⟨h3, h4.trans hS⟩]
        simp only [WMesh.areaVec, h5, h6, smul_neg, add_neg_cancel]
      · rw [if_neg (fun h => hS h.2), if_neg (fun h => hS (h4 ▸ h.2))]; simp
    · have hg : g p = p := if_neg hp
      rw [hg, if_neg (fun h => hp h.1)]; simp
  · intro p hp
    by_cases hb : bd p = false
    · have hg : g p = σ p := if_pos hb
      rw [hg]; exact (hσ p hb).2.1
    · exact absurd (if_neg (fun h => hb h.1)) hp
  · intro p
    by_cases hb : bd p = false
    · obtain ⟨h1, -, h3, -⟩ := hσ p hb
      have hg : g p = σ p := if_pos hb
      have hg' : g (σ p) = σ (σ p) := if_pos h3
      rw [hg, hg', h1]
    · have hg : g p = p := if_neg hb
      rw [hg, hg]

theorem diamond_balanced : diamond.FacetBalanced bd := balanced_of_conforming _ _ diamond_conforming

/-! ### The complete-scheme data on the diamond, for any admissible nodal states. -/

theorem phq_nonneg : ∀ q k, 0 ≤ phq q k := by
  intro q k; fin_cases q <;> fin_cases k <;> simp [phq, na, nb]

theorem phq_sum : ∀ q, ∑ k, phq q k = 1 := by
  intro q; rw [Fin.sum_univ_five]; fin_cases q <;> simp [phq, na, nb] <;> norm_num

theorem wE_neg (g : Gas) (U : State 2) (h : Admissible g U) : entropyVars g U .energy < 0 := by
  simp only [entropyVars]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos h.1) h.2

theorem proj_energy (g : Gas) (u : Fin 5 → State 2) (hu : ∀ i, Admissible g (u i)) (q : Fin 4 × Fin 3) :
    (∑ k, phq q k • entropyVars g (u k)) .energy < 0 :=
  Paper1.Proofs.p2_8_0b (Fin 5) 2 (fun k => entropyVars g (u k)) (phq q) (fun k => wE_neg g _ (hu k))
    (phq_nonneg q) (phq_sum q)

def utq (g : Gas) (u : Fin 5 → State 2) (hu : ∀ i, Admissible g (u i)) (q : Fin 4 × Fin 3) : State 2 :=
  Classical.choose (Paper1.Proofs.p2_8_0 2 g _ (proj_energy g u hu q)).exists

theorem utq_spec (g : Gas) (u : Fin 5 → State 2) (hu : ∀ i, Admissible g (u i)) (q : Fin 4 × Fin 3) :
    Admissible g (utq g u hu q) ∧ entropyVars g (utq g u hu q) = ∑ k, phq q k • entropyVars g (u k) :=
  Classical.choose_spec (Paper1.Proofs.p2_8_0 2 g _ (proj_energy g u hu q)).exists

/-- Non-trivial dissipation coefficients and viscosity, slip-free wall data `P = 0`, no wall faces. -/
def Sd (g : Gas) (u : Fin 5 → State 2) (hu : ∀ i, Admissible g (u i)) :
    Scheme.Data (Fin 5) (Fin 4) (Fin 4 × Fin 3) 2 where
  M := diamond
  g := g
  lam := fun _ _ => 1
  eps2 := fun _ _ => 1
  eps4 := fun _ _ => 1
  Nstar := fun _ => Finset.univ
  φ := phq
  N := fun q => aq q • diamond.areaVec (fq q)
  ut := utq g u hu
  Fs := fun _ => 0
  Pv := fun _ => ⟨1, 1, 1⟩
  P := 0
  gw := 0
  walls := fun _ => ∅
  c := 1

theorem schemeHyp_diamond (g : Gas) (u : Fin 5 → State 2) (hu : ∀ i, Admissible g (u i)) :
    Spec.SchemeHyp (Sd g u hu) bd fq aq u := by
  refine ⟨diamond_valid, by norm_num, by norm_num, diamond_balanced, hu, fun q => (utq_spec g u hu q).1, fq_bd,
    phq_supp, simpson_H1, simpson_H2, fun q => rfl, phq_sum, fun q => (utq_spec g u hu q).2,
    fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => ⟨zero_le_one, zero_le_one, zero_le_one⟩,
    fun _ => ⟨zero_le_one, zero_le_one, zero_lt_one⟩, Matrix.transpose_zero, Matrix.zero_mul 0,
    Matrix.zero_mulVec 0⟩

/-- The wall projector of a real no-slip wall (`momProj`, `gw = 0`) also meets the projector part of `SchemeHyp`
(P2-9.3 gives `WallHyp` for it). -/
example (d : ℕ) (Pv : ViscParams) (wb : State d) (hd : 1 ≤ d) (hd3 : d ≤ 3) (hR : 0 < Pv.R) (hE : wb .energy < 0) :
    (Spec.momProj d).transpose = Spec.momProj d ∧ Spec.momProj d * Spec.momProj d = Spec.momProj d ∧
    (Spec.momProj d).mulVec 0 = 0 := by
  obtain ⟨⟨-, -, -, h1, h2, h3⟩, -⟩ := Paper1.Proofs.p2_9_3 d ⟨Pv.R, 1, 0⟩ wb (fun _ => 1) hd hd3 one_pos le_rfl hR hE
    (fun h => by simpa using congrFun h ⟨0, hd⟩)
  exact ⟨h1, h2, h3⟩

#print axioms schemeHyp_diamond

end ReviewP3
