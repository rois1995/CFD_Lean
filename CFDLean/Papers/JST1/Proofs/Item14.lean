import CFDLean.Papers.JST1.Spec.Item14
import CFDLean.Papers.JST1.Proofs.Item1
import CFDLean.Papers.JST1.Proofs.Item2Generic
import CFDLean.Papers.JST1.Proofs.Item2Euler
import CFDLean.Papers.JST1.Proofs.Item6
import CFDLean.Papers.JST1.Proofs.Item8
import CFDLean.Papers.JST1.Proofs.Item9
import CFDLean.Papers.JST1.Proofs.Viscous
import CFDLean.Papers.JST1.Proofs.MeshAlgebra
import CFDLean.Papers.JST1.Proofs.Item11a
import CFDLean.Papers.JST1.Proofs.Addendum2

/-! Proofs of item 14 (P3): `thm:complete` (paper lines 530-548, proof 1165-1177) for the complete scheme of
`CFDLean/Papers/JST1/Scheme/Complete.lean`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs
namespace Cmp14
open CFDLean.JST1.Scheme

/-! ### Mesh facts -/

section Mesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

theorem n_anti (i k : ι) : M.n k i = -M.n i k := by
  unfold WMesh.n
  rw [neg_sub]

/-- `Σ_k n_ik = -β_i` for the median dual (P2-6.1, no mesh hypothesis). -/
theorem n_row (i : ι) : ∑ k, M.n i k = -M.beta i := by
  have hW : ∀ T, ∑ _a : Fin (d + 1), M.m T = M.vol T := by
    intro T
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, WMesh.m]
    push_cast
    field_simp
  obtain ⟨-, -, -, h1, h2⟩ := p2_6_1 ι C d M (fun T _ => M.m T) hW
  simp only [WMesh.n, WMesh.c, Finset.sum_sub_distrib, h1, h2, zero_sub]

/-- Facet-balanced form of P2-8.4(i): the face rule reproduces `β` (via P3-11.1). -/
theorem phiN_beta {Q : Type} [Fintype Q] [DecidableEq C] (bd : C × Fin (d + 1) → Bool)
    (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ) (φ : Q → ι → ℝ) (N : Q → Vec d) (hV : M.Valid) (hd : 1 ≤ d)
    (hF : M.FacetBalanced bd) (hbdq : ∀ q, bd (fq q) = true)
    (hφz : ∀ q k, k ∉ M.facetNodes (fq q) → φ q k = 0)
    (hH1 : ∀ p, bd p = true → ∀ i ∈ M.facetNodes p, (∑ q, if fq q = p then aq q * φ q i else 0) = 1 / (d : ℝ))
    (hN : ∀ q, N q = aq q • M.areaVec (fq q)) (i : ι) :
    ∑ q, φ q i • N q = M.beta i := by
  rw [((p3_11_1 ι C d M bd hV hd).2 hF).1 i]
  have hzero : ∀ p (f : Q → ℝ), (∀ q, fq q = p → f q = 0) → (∑ q, if fq q = p then f q else 0) = 0 :=
    fun p f hf => Finset.sum_eq_zero fun q _ => by split_ifs with h <;> simp [hf q, h]
  have e : ∀ q, φ q i • N q = (aq q * φ q i) • M.areaVec (fq q) := fun q => by
    rw [hN q, smul_smul, mul_comm]
  simp only [e]
  rw [Cl8.regroup]
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

end Mesh

/-! ### The scheme -/

section Scheme
variable {ι C Q : Type} [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype Q] {d : ℕ} (S : Data ι C Q d)
  (u : ι → State d)

theorem central_anti (i k : ι) : central S u k i = -central S u i k := by
  unfold central
  rw [(p1_2_5 d S.g).2.1 (u k) (u i), n_anti]
  exact map_neg (IsLinearMap.mk' _ ((p1_2_5 d S.g).2.2.1 (u i) (u k))) (S.M.n i k)

theorem diss2_anti (hsym : ∀ i k, S.lam k i = S.lam i k ∧ S.eps2 k i = S.eps2 i k ∧ S.eps4 k i = S.eps4 i k)
    (i k : ι) : diss2 S u k i = -diss2 S u i k := by
  unfold diss2
  rw [(hsym i k).1, (hsym i k).2.1, ← neg_sub, smul_neg]

theorem diss4_anti (hsym : ∀ i k, S.lam k i = S.lam i k ∧ S.eps2 k i = S.eps2 i k ∧ S.eps4 k i = S.eps4 i k)
    (i k : ι) : diss4 S u k i = -diss4 S u i k := by
  unfold diss4
  rw [(hsym i k).1, (hsym i k).2.2, ← neg_sub, smul_neg]

/-- Central part: `-Σ_i w_i·Σ_k F^ec_ik = Σ_i ψ_i·β_i` (P1-2.2 with P1-2.5, P2-6.1). -/
theorem central_part (hu : ∀ i, Admissible S.g (u i)) :
    -(∑ i, pairF (w S u i) (∑ k, central S u i k)) = ∑ i, Num.dot (fluxPot (u i)) (S.M.beta i) := by
  have h := p1_2_2 ι {U : State d // Admissible S.g U} (Channel d) d (fun a => entropyVars S.g a.1)
    (fun a => fluxPot a.1) (fun a b y => ismailRoe S.g a.1 b.1 y) S.M.n (fun i => ⟨u i, hu i⟩)
    (fun i k => n_anti S.M i k) (fun a b y => (p1_2_5 d S.g).2.1 a.1 b.1 y)
    (fun a b => (p1_2_5 d S.g).2.2.1 a.1 b.1) (fun a b y => (p1_2_5 d S.g).1 a.1 b.1 y a.2 b.2)
  obtain ⟨h1, h2⟩ := h
  refine (h1.trans h2).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [n_row, neg_neg]

/-- Closure: `-Σ_i w_i·b_i = B - Σ_i ψ_i·Σ_q φ_qi N_q` (P2-8.1). -/
theorem closure_part (hu : ∀ i, Admissible S.g (u i)) (hut : ∀ q, Admissible S.g (S.ut q))
    (hφ1 : ∀ q, ∑ k, S.φ q k = 1)
    (hwut : ∀ q, entropyVars S.g (S.ut q) = ∑ k, S.φ q k • entropyVars S.g (u k)) :
    -(∑ i, pairF (w S u i) (closure S u i)) =
      Bterm S - ∑ i, Num.dot (fluxPot (u i)) (∑ q, S.φ q i • S.N q) := by
  have h := (p2_8_1 ι Q {U : State d // Admissible S.g U} (Channel d) d (fun a => entropyVars S.g a.1)
    (fun a => fluxPot a.1) (fun a b y => ismailRoe S.g a.1 b.1 y) (fun i => ⟨u i, hu i⟩) S.φ S.N
    (fun q => ⟨S.ut q, hut q⟩) S.Fs (fun a b y => (p1_2_5 d S.g).2.1 a.1 b.1 y)
    (fun a b y => (p1_2_5 d S.g).1 a.1 b.1 y a.2 b.2) hφ1 hwut).1
  have h' : ∑ i, Num.dot (fluxPot (u i)) (∑ q, S.φ q i • S.N q) - ∑ i, pairF (w S u i) (closure S u i) = Bterm S := by
    rw [← Finset.sum_sub_distrib]
    exact h
  linarith

/-- The viscous and wall residuals, written per element. -/
theorem vw_local (i : ι) :
    visc S u i + wall S u i = ∑ T, ∑ a, if S.M.vert T a = i then S.M.ω T •
      (Wall.Rvisc (S.M.simplex T) (K S u T) (wloc S u T) a +
        Wall.Rwall (S.M.simplex T) (K S u T) S.P S.gw (S.walls T) S.c (wloc S u T) a) else 0 := by
  have hg : ∀ T, S.M.gradW (w S u) T = Wall.gradT (S.M.simplex T) (wloc S u T) := fun T => rfl
  unfold visc wall WMesh.galerkinRes
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · beta_reduce
    rw [hg, smul_add]
    congr 1
    unfold Wall.Rvisc
    rw [smul_neg, smul_smul]
    rfl
  · simp

theorem vw_pair :
    ∑ i, pairF (w S u i) (visc S u i + wall S u i) = ∑ T, S.M.ω T * ∑ b, pairF (wloc S u T b)
      (Wall.Rvisc (S.M.simplex T) (K S u T) (wloc S u T) b +
        Wall.Rwall (S.M.simplex T) (K S u T) S.P S.gw (S.walls T) S.c (wloc S u T) b) := by
  simp only [vw_local, Cl8.pr_sum]
  have e : ∀ i T a, pairF (w S u i) (if S.M.vert T a = i then S.M.ω T •
      (Wall.Rvisc (S.M.simplex T) (K S u T) (wloc S u T) a +
        Wall.Rwall (S.M.simplex T) (K S u T) S.P S.gw (S.walls T) S.c (wloc S u T) a) else 0) =
      if S.M.vert T a = i then S.M.ω T * pairF (wloc S u T a)
      (Wall.Rvisc (S.M.simplex T) (K S u T) (wloc S u T) a +
        Wall.Rwall (S.M.simplex T) (K S u T) S.P S.gw (S.walls T) S.c (wloc S u T) a) else 0 := by
    intro i T a
    split_ifs with h
    · subst h
      rw [Cl8.pr_smul]
      rfl
    · simp [pairF]
  simp only [e]
  rw [sum_single (X := ℝ) S.M]
  simp only [Finset.mul_sum]

/-- `w̄_T` has negative energy component. -/
theorem wbar_neg (hV : S.M.Valid) (hd3 : d ≤ 3) (hu : ∀ i, Admissible S.g (u i))
    (hPv : ∀ T, 0 ≤ (S.Pv T).μ ∧ 0 ≤ (S.Pv T).κ ∧ 0 < (S.Pv T).R) (T : C) :
    wbar S u T .energy < 0 :=
  (p1_4_3 ι C d S.M (S.Pv T) (w S u) hV hd3 (hPv T).1 (hPv T).2.1 (hPv T).2.2
    (fun i => p1_4_3b d S.g (u i) (hu i))).1 T

theorem wallHyp (hV : S.M.Valid) (hd3 : d ≤ 3) (hu : ∀ i, Admissible S.g (u i))
    (hPv : ∀ T, 0 ≤ (S.Pv T).μ ∧ 0 ≤ (S.Pv T).κ ∧ 0 < (S.Pv T).R) (hPT : S.P.transpose = S.P)
    (hPP : S.P * S.P = S.P) (hPg : S.P.mulVec S.gw = S.gw) (T : C) :
    Spec.WallHyp (K S u T) S.P S.gw := by
  have hE := wbar_neg S u hV hd3 hu hPv T
  have h42 := p1_4_2 d (S.Pv T) (wbar S u T) hd3 (hPv T).1 (hPv T).2.1 (hPv T).2.2 hE
  exact ⟨h42.2, fun G H => p1_4_4 d (S.Pv T) (wbar S u T) G H hE.ne, h42.1, hPT, hPP, hPg⟩

end Scheme

end Cmp14

open Cmp14 CFDLean.JST1.Scheme

theorem p3_14_1 : Spec.P3_14_1 := by
  intro ι C Q _ _ _ _ _ d S bd fq aq u hS
  obtain ⟨hV, hd1, hd3, hF, hu, hut, hbdq, hφz, hH1, -, hN, hφ1, hwut, hsym, hnn, hPv, hPT, hPP, hPg⟩ := hS
  have hWH := wallHyp S u hV hd3 hu hPv hPT hPP hPg
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the balance identity
    have hsplit : ∀ i, pairF (w S u i) (resid S u i) =
        -pairF (w S u i) (∑ k, central S u i k) - pairF (w S u i) (∑ k, diss2 S u i k) +
          pairF (w S u i) (∑ k, diss4 S u i k) - pairF (w S u i) (closure S u i) +
          pairF (w S u i) (visc S u i + wall S u i) := by
      intro i
      unfold resid
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Cl8.pr_add, Cl8.pr_sub, pairF_neg_right]
      ring
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    have hc := central_part S u hu
    have hb := closure_part S u hu hut hφ1 hwut
    have hβ : ∀ i, ∑ q, S.φ q i • S.N q = S.M.beta i :=
      phiN_beta S.M bd fq aq S.φ S.N hV hd1 hF hbdq hφz hH1 hN
    simp only [hβ] at hb
    have h2 : -(∑ i, pairF (w S u i) (∑ k, diss2 S u i k)) = Pi2 S u :=
      (p1_2_1 ι (Channel d) (diss2 S u) (w S u) (diss2_anti S u hsym)).2
    have h4 : -(∑ i, pairF (w S u i) (∑ k, diss4 S u i k)) = -Pi4 S u :=
      (p1_2_1 ι (Channel d) (diss4 S u) (w S u) (diss4_anti S u hsym)).2.trans (by unfold Pi4; ring)
    have hvw : ∑ i, pairF (w S u i) (visc S u i + wall S u i) =
        -(∑ T, S.M.ω T * (Dg S u T - Pw S u T)) + wallFlux S u := by
      rw [vw_pair]
      unfold wallFlux
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [p2_9_0 (Channel d) d (S.M.simplex T) (K S u T) S.P S.gw (S.walls T) S.c (wloc S u T) (hWH T)]
      unfold Dg Pw
      ring
    rw [hvw]
    linarith
  · -- Π^(2) ≤ 0
    unfold Pi2
    refine mul_nonpos_of_nonneg_of_nonpos (by norm_num) ?_
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun k _ => ?_
    obtain ⟨-, h1, h2⟩ := p1_1_5 d S.g (u i) (u k) (S.lam i k) (S.eps2 i k) (hu i) (hu k) (hnn i k).1
      (hnn i k).2.1
    exact h1.trans h2
  · -- element bound
    intro hc T
    exact (p2_9_1 (Channel d) d (S.M.simplex T) (K S u T) S.P S.gw (S.walls T) S.c (wloc S u T) (hWH T) hd1
      (hV.2 T) (by linarith)).2 hc
  · -- antisymmetry of the pair fluxes
    intro i k
    rw [central_anti, diss2_anti S u hsym, diss4_anti S u hsym]
    abel

theorem p3_14_2 : Spec.P3_14_2 := by
  intro ι C Q _ _ _ _ d S slip ug hut hslip hfar
  unfold Bterm
  refine Finset.sum_le_sum fun q _ => ?_
  cases h : slip q
  · simp only [Bool.false_eq_true, ite_false]
    exact (p2_8_6).1 (State d) (Channel d) d (entropyVars S.g) fluxPot (S.ut q) (ug q) (S.N q) (S.Fs q)
      (hfar q h)
  · simp only [ite_true]
    rw [hslip q h]
    exact (p2_8_5 d S.g (S.ut q) (S.N q) (hut q)).le

theorem p3_14_3 : Spec.P3_14_3 := by
  intro ι C Q _ _ _ _ _ d S bd fq aq Ut Vv R t X Ck Bk Dh Sk Rrho Pst inD kD Dt u hS hV hU β2 Rk hR hP hX hSk hD
    hDt hW
  have hbal := (p3_14_1 ι C Q d S bd fq aq u hS).1
  have hVd := hS.1
  have hu := hS.2.2.2.2.1
  have hbal' : -(∑ i, pairF (entropyVars S.g (hatState (Ut i t))) (-resid S u i)) ≤
      Bterm S + wallFlux S u + Pi2 S u + Pi4 S u - ∑ T, (S.M.ω T * Dg S u T - S.M.ω T * Pw S u T) := by
    have e1 : ∑ i, pairF (entropyVars S.g (hatState (Ut i t))) (-resid S u i) =
        -∑ i, pairF (w S u i) (resid S u i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => pairF_neg_right _ _
    have e2 : ∑ T, (S.M.ω T * Dg S u T - S.M.ω T * Pw S u T) = ∑ T, S.M.ω T * (Dg S u T - Pw S u T) :=
      Finset.sum_congr rfl fun T _ => by ring
    rw [e1, e2, neg_neg, hbal]
    linarith
  have hW' : ∀ T, S.M.ω T * Pw S u T ≤ S.M.ω T * Dg S u T - S.M.ω T * Dt T := by
    intro T
    have := mul_le_mul_of_nonneg_left (hW T) (hVd.1 T)
    linarith
  obtain ⟨r, hr, hle⟩ := p2_10_8c ι C d S.g Ut Vv R t (fun i => -resid S u i) X Ck Bk Dh Sk Rrho Pst inD kD
    (fun T => S.M.ω T * Dg S u T) (fun T => S.M.ω T * Dt T) (fun T => S.M.ω T * Pw S u T)
    (Bterm S + wallFlux S u) (Pi2 S u) (Pi4 S u) hu hV hU hR hP hbal' hX hSk hD hDt hW'
  refine ⟨r, hr, le_of_le_of_eq hle ?_⟩
  have e : ∑ T, (S.M.ω T * Dg S u T - S.M.ω T * Dt T - S.M.ω T * Pw S u T) =
      ∑ T, S.M.ω T * (Dg S u T - Dt T - Pw S u T) :=
    Finset.sum_congr rfl fun T _ => by ring
  rw [e]

end CFDLean.JST1.Proofs
