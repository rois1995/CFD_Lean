import Paper1
import Paper1.Proofs.GeomBase
import Paper1.Proofs.Simplex
import Paper1.Proofs.Item6
import Paper1.Proofs.Item8
import Paper1.Proofs.Item9

/-! Reviewer's non-vacuity checks for the P2 statements (independent review, not part of the build).
Compile with `lake env lean reviews/P2/NonVacuity.lean`. The diamond mesh is copied from `reviews/P1/NonVacuity.lean`. -/
noncomputable section
open scoped BigOperators
open NumCore Paper1

namespace ReviewP2

/-! ### 0. Gradient helper (from the P1 review). -/

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

/-- P2-6.3 applied: the centre is closed, through the conforming hypothesis (non-vacuous). -/
example : diamond.Closed 4 :=
  (Paper1.Proofs.p2_6_3 (Fin 5) (Fin 4) 2 diamond bd diamond_valid (by norm_num) diamond_conforming).2.2 4
    centre_off_boundary

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

/-- P2-8.4 applied: the Simpson rule gives `Σ_q φ_qi N_q = β_i` on the diamond (non-vacuous). -/
example : ∀ i, ∑ q, phq q i • (aq q • diamond.areaVec (fq q)) = diamond.beta i :=
  (Paper1.Proofs.p2_8_4 (Fin 5) (Fin 4) (Fin 4 × Fin 3) 2 diamond bd fq aq phq diamond_valid (by norm_num)
    diamond_conforming fq_bd phq_supp simpson_H1 simpson_H2).1

/-! ### 4. `WallHyp` and the sharpness example of P2-9.2 are non-vacuous. -/

/-- The identity map with the identity projector meets `WallHyp` (any data `gw`). -/
example {κ : Type} [Fintype κ] [DecidableEq κ] {d : ℕ} (gw : κ → ℝ) :
    Paper1.Spec.WallHyp (fun G : Matrix κ (Fin d) ℝ => G) (1 : Matrix κ κ ℝ) gw := by
  refine ⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩, ?_, ?_, Matrix.transpose_one, Matrix.one_mul 1, Matrix.one_mulVec gw⟩
  · intro G H; unfold frob; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · intro G; unfold frob; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- Reference triangle `(0,0), (1,0), (0,1)`. -/
def refT : Simplex 2 := ⟨![![0, 0], ![1, 0], ![0, 1]]⟩

theorem refT_nondeg : refT.Nondeg := by
  simp [Simplex.Nondeg, Simplex.edgeMat, refT, Matrix.det_fin_two]

theorem refT_grad0 : refT.grad 0 = ![-1, -1] := by
  apply grad_eq _ refT_nondeg
  intro b; fin_cases b <;> simp [dot, Fin.sum_univ_two, refT]

theorem refT_normal_ne : Paper1.Wall.normal refT 0 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have hl : 0 < len (refT.grad 0) := by
    rw [refT_grad0]; unfold len dot; apply Real.sqrt_pos.2; simp [Fin.sum_univ_two]
  simp only [Paper1.Wall.normal, refT_grad0, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
  simp at h0
  exact absurd h0 (ne_of_gt (by rw [refT_grad0] at hl; positivity))

def wb0 : State 2 := -eE

/-- The Navier-Stokes `K` (μ = 1, κ = 0, R = 1) at `w̄_E = -1` with the momentum projector: the hypotheses of
P2-9.2 hold, and the theorem produces nodal values with `D^gal - Π^w < 0` for `c = 1/2`. -/
example : ∃ w : Fin 3 → State 2,
    Paper1.Wall.Dgal refT (viscFlux ⟨1, 1, 0⟩ wb0) w -
      Paper1.Wall.PiW refT (viscFlux ⟨1, 1, 0⟩ wb0) (Paper1.Spec.momProj 2) 0 {0} (1 / 2) w < 0 := by
  have hwb : wb0 .energy < 0 := by simp [wb0, eE]
  obtain ⟨hW, e, hPe, hz⟩ := Paper1.Proofs.p2_9_3 2 ⟨1, 1, 0⟩ wb0 (Paper1.Wall.normal refT 0) (by norm_num)
    (by norm_num) one_pos le_rfl one_pos hwb refT_normal_ne
  exact Paper1.Proofs.p2_9_2 (Channel 2) 2 refT _ _ 0 0 (1 / 2) e hW (by norm_num) refT_nondeg (by norm_num)
    (by norm_num) hPe hz

/-! ### 5. Statements that are true for elementary reasons (proved here without the project's proofs). -/

/-- P2-8.6, first part: a rearrangement of the hypothesis. -/
example : ∀ (S κ : Type) [Fintype κ] (d : ℕ) (w : S → κ → ℝ) (ψ : S → Vec d) (ut ug : S) (N : Vec d)
    (Fs : κ → ℝ), pairF (w ug - w ut) Fs ≤ dot (ψ ug - ψ ut) N →
    dot (ψ ut) N - pairF (w ut) Fs ≤ dot (ψ ug) N - pairF (w ug) Fs := by
  intro S κ _ d w ψ ut ug N Fs h
  simp only [pairF, dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] at *
  linarith

/-- P2-10.6. -/
example : Paper1.Spec.P2_10_6 := by
  intro Pst cl ε hε hP
  have : max 0 (min Pst (cl * ε)) ≤ Pst + ε := max_le (by linarith) ((min_le_left _ _).trans (by linarith))
  linarith

/-- P2-10.8, second part (the two sufficient conditions for `(W_t)`). -/
example : ∀ (Dgal Dt PiW c : ℝ),
    (PiW = 0 → Dt ≤ Dgal → PiW ≤ Dgal - Dt) ∧
    (0 < c → PiW ≤ Dgal / c → Dt ≤ (1 - 1 / c) * Dgal → PiW ≤ Dgal - Dt) := by
  intro Dgal Dt PiW c
  refine ⟨fun h1 h2 => by linarith, fun _ h2 h3 => ?_⟩
  have : (1 - 1 / c) * Dgal = Dgal - Dgal / c := by ring
  linarith

end ReviewP2
