import CFDLean.Papers.JST1.Proofs.Item23Conf
import CFDLean.Papers.JST1.Proofs.Item23Sum

/-! Proofs of item 23 (P8): the Kuhn-split and interior-vertex extensions of the G8 counterexample. A layered cell
(unit square at height `z0`, top face its affine image `A p + t` at height `z0 + 1`) has the trilinear map
`(1-w)(b+(u,v)) + w(A(b+(u,v)) + t)` and Jacobian determinant `det((1-w) I + w A)`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs
namespace Ext23

open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec Asm11

end Ext23


open Ext23 CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec in
theorem p8_23_1 : Spec.P8_23_1 := by
  refine ⟨?_, fun ξ _ => ?_, ?_⟩
  · rw [kuhnX_eq]; exact vertices_lay _ _ _ _ _ _ _ _ _
  · rw [kuhnX_eq, det_lay]
    nlinarith [sq_nonneg (ξ 2 - 1 / 2)]
  · refine ⟨(0, [false, false, false, false, true, false]), by decide, [0, 4, 5, 6], by decide, [0, 1, 6, 5],
      by decide, [0, 5, 6], by decide, by decide, by decide, by decide, ?_⟩
    have e1 : oppV ([0, 4, 5, 6] : List (Fin 8)) [0, 5, 6] 0 = 4 := by decide
    have e2 : oppV ([0, 1, 6, 5] : List (Fin 8)) [0, 5, 6] 0 = 1 := by decide
    rw [e1, e2]
    simp only [sideF, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [sideOf, cross, Num.dot, Fin.sum_univ_three, kuhnX]

namespace Ext23
open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec Asm11

theorem side_b (a b d x : Fin 27) :
    sideOf (blockPos a) (blockPos b) (blockPos d) (blockPos x) =
      (1 / 5 : ℝ) ^ 3 * (sideZ (bZ a) (bZ b) (bZ d) (bZ x) : ℝ) := by
  rw [blockPos_eq, blockPos_eq, blockPos_eq, blockPos_eq, Twist22.sideOf_smul, sideOf_cast]

theorem nondeg_b (x : Σ c : Fin 8, Fin (blockMesh.cell c).kind.tets.length) : (blockMesh.toW.simplex x).Nondeg := by
  have h1 := List.all_eq_true.mp (chk_nondeg_b x.1) (bT x) (tet_mem_b x)
  simp only [bne_iff_ne, ne_eq] at h1
  have hs : blockMesh.toW.simplex x = ⟨fun a => blockPos (blockIdx x.1 ((bT x).getD a 0))⟩ := by
    unfold WMesh.simplex
    rw [show blockMesh.toW.pos = blockPos from rfl]
    simp only [vert_b]
  rw [hs, Simplex.Nondeg, Geo3.det_edge3]
  show sideOf _ _ _ _ ≠ 0
  simp only [side_b, Fin.coe_ofNat_eq_mod, Nat.reduceMod]
  exact mul_ne_zero (by norm_num) (by exact_mod_cast h1)

theorem area_b (p : (Σ c : Fin 8, Fin (blockMesh.cell c).kind.tets.length) × Fin 4) :
    blockMesh.toW.areaVec p = (-(1 / 3200) : ℝ) • castZ3 (AZB p.1.1 (bT p.1) p.2) := by
  have hd1 := List.all_eq_true.mp Twist22.chk_dist (bT p.1) (tet_mem_b p.1)
  have hd2 := List.all_eq_true.mp hd1 p.2 (List.mem_finRange _)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hd2
  obtain ⟨⟨h01, h02⟩, h12⟩ := hd2
  have inj := blockIdx_inj p.1.1
  have hS := nodes_b p
  rw [WMesh.areaVec, facetVec_any blockMesh.toW p (nondeg_b p.1) _ _ _ (fun e => h01 (inj e))
    (fun e => h02 (inj e)) (fun e => h12 (inj e)) hS]
  rw [show blockMesh.toW.pos = blockPos from rfl, vert_b, side_b, sg_mul,
    show sg ((1 / 5 : ℝ) ^ 3) = 1 by simp [sg], one_mul, sg_int,
    show blockMesh.toW.ω p.1 = 1 / 64 by
      show Kind.hex.w = 1 / 64
      rw [Kind.w, Twist22.splits_len]]
  rw [blockPos_eq, blockPos_eq, blockPos_eq]
  ext α
  fin_cases α <;> simp [AZB, Twist22.smulZ, cross3, castZ3, crsZ, subZ] <;> ring

set_option maxRecDepth 10000 in
theorem sum_b (Q : Fin 8 → List (Fin 8) → Fin 4 → Bool) :
    (∑ p : (Σ c : Fin 8, Fin (blockMesh.cell c).kind.tets.length) × Fin 4,
      if Q p.1.1 (bT p.1) p.2 = true then blockMesh.toW.areaVec p else 0) =
      (-(1 / 3200) : ℝ) • castZ3 (((List.finRange 8).map fun c => intSB c (Q c)).sum) := by
  have e : ∀ p : (Σ c : Fin 8, Fin (blockMesh.cell c).kind.tets.length) × Fin 4,
      (if Q p.1.1 (bT p.1) p.2 = true then blockMesh.toW.areaVec p else 0) =
      (-(1 / 3200) : ℝ) • Twist22.castHom (if Q p.1.1 (bT p.1) p.2 = true then AZB p.1.1 (bT p.1) p.2 else 0) := by
    intro p
    split_ifs
    · rw [area_b]; rfl
    · simp
  rw [Finset.sum_congr rfl fun p _ => e p, ← Finset.smul_sum, ← map_sum,
    show (⇑Twist22.castHom : Z3 → Vec 3) = castZ3 from rfl]
  refine congrArg (fun z : Z3 => (-(1 / 3200) : ℝ) • castZ3 z) ?_
  rw [Fintype.sum_prod_type, Fintype.sum_sigma]
  have hO : ∀ (c : Fin 8) (t : List (Fin 8)), ∑ o : Fin 4, (if Q c t o = true then AZB c t o else 0) =
      ((List.finRange 4).map fun o => if Q c t o = true then AZB c t o else 0).sum := by
    intro c t
    rw [List.finRange, List.map_ofFn, List.sum_ofFn]
    rfl
  have hC : ∀ c : Fin 8, (∑ j : Fin (blockMesh.cell c).kind.tets.length, ∑ o : Fin 4,
      (if Q c (bT ⟨c, j⟩) o = true then AZB c (bT ⟨c, j⟩) o else 0)) = intSB c (Q c) := by
    intro c
    simp only [hO]
    unfold intSB
    exact Twist22.sum_list (α := List (Fin 8)) (β := Z3) (Kind.hex.tets : List (List (Fin 8)))
      (fun t => ((List.finRange 4).map fun o => if Q c t o = true then AZB c t o else 0).sum)
  simp only [hC]
  rw [List.finRange, List.map_ofFn, List.sum_ofFn]
  rfl

theorem chk_13bd : ∀ S ∈ bdTrisOf blockMesh, (13 : Fin 27) ∉ S := by
  intro S hS h13
  have hS' := hS
  simp only [bdTrisOf, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and] at hS'
  obtain ⟨⟨c, hc⟩, -⟩ := hS'
  simp only [faceSets, List.mem_toFinset, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  exact chk_13nb c p hp h13 hS

end Ext23

open Ext23 Asm11 CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec in
theorem p8_23_2 : Spec.P8_23_2 := by
  refine ⟨fun c a => ?_, fun c ξ _ => ?_, fun c S fl h => ?_, chk_13bd, ?_⟩
  · rw [blockX_eq]; split_ifs <;> exact vertices_lay _ _ _ _ _ _ _ _ _ a
  · rw [blockX_eq]
    split_ifs
    · rw [det_lay]; nlinarith
    · rw [det_lay]; nlinarith [sq_nonneg (ξ 2 - 1 / 2)]
  · by_cases hS : S ∈ bdTrisOf blockMesh
    · exact Or.inl ⟨hS, fun c' hc' fl' h' => hc' (bd_unique blockMesh hS (mem_faceSets _ h) (mem_faceSets _ h'))⟩
    · obtain ⟨c', hne, hm, hu⟩ := chk_int c (S, fl) h hS
      refine Or.inr ⟨hS, c', hne, hm, hu, fun xa xb xc hx => ?_⟩
      have hz := chk_geo c c' hne (S, fl) h hm xa (by rw [hx]; simp) xb (by rw [hx]; simp) xc (by rw [hx]; simp) hx
      rw [side_cen_b, side_cen_b]
      have e : (1 / 5 : ℝ) ^ 3 * ((1 / ((8 : ℕ) : ℝ)) * (EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c) : ℝ)) *
          ((1 / 5 : ℝ) ^ 3 * ((1 / ((8 : ℕ) : ℝ)) * (EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c') : ℝ))) =
          ((1 / 5 : ℝ) ^ 3 * (1 / ((8 : ℕ) : ℝ))) ^ 2 *
            ((EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c) : ℝ) * (EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c') : ℝ)) := by ring
      rw [e]
      exact mul_neg_of_pos_of_neg (by positivity) (by exact_mod_cast hz)
  · have hn : ∑ k, blockMesh.toW.n 13 k = -blockMesh.toW.beta 13 := by
      simp only [WMesh.n, Finset.sum_sub_distrib, CFDLean.Num.Internal.Sbp6.c_row, CFDLean.Num.Internal.Sbp6.c_col,
        zero_sub]
    have hb := Twist22.beta_all blockMesh.toW (d := 3) (by norm_num) 13
    have e : ∀ p : (Σ c : Fin 8, Fin (blockMesh.cell c).kind.tets.length) × Fin 4,
        (if (13 : Fin 27) ∈ blockMesh.toW.facetNodes p then (1 / ((3 : ℕ) : ℝ)) • blockMesh.toW.areaVec p else 0) =
        (1 / ((3 : ℕ) : ℝ)) • if (fun c t o => decide (13 ∈ nodesB c t o)) p.1.1 (bT p.1) p.2 = true then
          blockMesh.toW.areaVec p else 0 := by
      intro p
      rw [nodes_b]
      by_cases h : (13 : Fin 27) ∈ nodesB p.1.1 (bT p.1) p.2
      · rw [ite_eq_left h, ite_eq_left (by simpa using h)]
      · rw [ite_eq_right h, ite_eq_right (by simpa using h), smul_zero]
    rw [hn, hb, Finset.sum_congr rfl fun p _ => e p, ← Finset.smul_sum,
      sum_b (fun c t o => decide (13 ∈ nodesB c t o)), chk_13]
    ext α
    fin_cases α <;> simp [castZ3] <;> norm_num

end CFDLean.JST1.Proofs
