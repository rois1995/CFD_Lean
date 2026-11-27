import CFDLean.Papers.JST1.Proofs.Item23Base

/-! Item 23 (P8), part 2: closed kernel checks of the conformity of the block and of the faces at vertex 13. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs
namespace Ext23

open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec Asm11
/-- `blockFT` with lists in place of finite sets (no `Finset` inside the kernel loop). -/
def blockFL (c : Fin 8) : List (List (Fin 27) × Bool) :=
  (RefCell.hex.quads.flatMap fun q => (q.tris false ++ q.tris true).map fun f => (f.map (blockIdx c), true)) ++
    RefCell.hex.tris.map fun f => (f.map (blockIdx c), false)

theorem blockFT_L (c : Fin 8) : blockFT c = (blockFL c).map fun p => (p.1.toFinset, p.2) := by
  simp only [blockFT, blockFL, List.map_append, List.map_flatMap, List.map_map, Function.comp_def]

/-- Every face at vertex 13 is also a face of a second cell, as one closed Boolean computation on lists. -/
def chk13B : Bool :=
  (List.finRange 8).all fun c => (blockFL c).all fun p => !(p.1.contains 13) ||
    (List.finRange 8).any fun c' => c' != c && (blockFL c').any fun q =>
      (List.finRange 27).all fun x => q.1.contains x == p.1.contains x

set_option maxHeartbeats 4000000 in
theorem chk_13B : chk13B = true := by decide +kernel

theorem chk_13L (c : Fin 8) (p : List (Fin 27) × Bool) (hp : p ∈ blockFL c) (h13 : (13 : Fin 27) ∈ p.1) :
    ∃ c' : Fin 8, c' ≠ c ∧ ∃ q ∈ blockFL c', ∀ x : Fin 27, x ∈ q.1 ↔ x ∈ p.1 := by
  have h := chk_13B
  simp only [chk13B, List.all_eq_true, List.any_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain h | ⟨c', -, hc, q, hq, hx⟩ := h c p hp
  · exact absurd (List.contains_iff_mem.mpr h13) (by rw [h]; decide)
  · exact ⟨c', hc, q, hq, fun x => by rw [← List.contains_iff_mem, ← List.contains_iff_mem, hx x]⟩

theorem not_bdF {c c' : Fin 8} (hc : c' ≠ c) {p : Finset (Fin 27) × Bool} {fl : Bool} (h1 : p ∈ blockFT c)
    (h2 : (p.1, fl) ∈ blockFT c') : p.1 ∉ bdF := by
  intro hS
  unfold bdF at hS
  rw [Finset.mem_filter] at hS
  have h : 1 < (Finset.univ.filter fun c => p.1 ∈ (blockFT c |>.map Prod.fst).toFinset).card := by
    rw [Finset.one_lt_card]
    refine ⟨c, ?_, c', ?_, hc.symm⟩ <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map]
    exacts [⟨p, h1, rfl⟩, ⟨(p.1, fl), h2, rfl⟩]
  omega

theorem chk_13nbF : ∀ c : Fin 8, ∀ p ∈ blockFT c, (13 : Fin 27) ∈ p.1 → p.1 ∉ bdF := by
  intro c p hp h13
  rw [blockFT_L, List.mem_map] at hp
  obtain ⟨l, hl, rfl⟩ := hp
  obtain ⟨c', hc, q, hq, hx⟩ := chk_13L c l hl (List.mem_toFinset.mp h13)
  have hS : q.1.toFinset = l.1.toFinset := by ext x; simp only [List.mem_toFinset, hx]
  refine not_bdF (fl := q.2) hc (by rw [blockFT_L]; exact List.mem_map_of_mem hl) ?_
  rw [← hS, blockFT_L]
  exact List.mem_map_of_mem hq

/-- The same vertex set, for two vertex lists. -/
def sameL (p q : List (Fin 27)) : Bool := p.all q.contains && q.all p.contains

theorem sameL_iff (p q : List (Fin 27)) : sameL p q = true ↔ p.toFinset = q.toFinset := by
  simp only [sameL, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Finset.ext_iff, List.mem_toFinset]
  exact ⟨fun ⟨h1, h2⟩ x => ⟨h1 x, h2 x⟩, fun h => ⟨fun x hx => (h x).1 hx, fun x hx => (h x).2 hx⟩⟩

theorem mem_blockFT {c : Fin 8} {S : Finset (Fin 27)} {fl : Bool} :
    (S, fl) ∈ blockFT c ↔ ∃ q ∈ blockFL c, q.1.toFinset = S ∧ q.2 = fl := by
  rw [blockFT_L, List.mem_map]
  constructor
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  · rintro ⟨q, hq, h1, h2⟩
    exact ⟨q, hq, by rw [h1, h2]⟩

/-- A face of exactly one cell is a boundary face. -/
theorem mem_bdF {c : Fin 8} {S : Finset (Fin 27)} {fl : Bool} (h : (S, fl) ∈ blockFT c)
    (hu : ∀ c' : Fin 8, c' ≠ c → ∀ fl' : Bool, (S, fl') ∉ blockFT c') : S ∈ bdF := by
  have hm : ∀ c', S ∈ (blockFT c' |>.map Prod.fst).toFinset ↔ c' = c := by
    intro c'
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨q, hq, hq1⟩
      by_contra hne
      exact hu c' hne q.2 (by rw [← hq1]; exact hq)
    · rintro rfl
      exact ⟨_, h, rfl⟩
  unfold bdF
  rw [Finset.mem_filter, Finset.mem_biUnion]
  refine ⟨⟨c, Finset.mem_univ _, (hm c).mpr rfl⟩, ?_⟩
  rw [Finset.card_eq_one]
  exact ⟨c, by ext c'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hm]⟩

/-- The other cells with a face of the vertex set `p`. -/
def hitsL (c : Fin 8) (p : List (Fin 27)) : List (Fin 8) :=
  (List.finRange 8).filter fun c' => c' != c && (blockFL c').any fun q => sameL p q.1

theorem mem_hitsL {c c' : Fin 8} {p : List (Fin 27)} :
    c' ∈ hitsL c p ↔ c' ≠ c ∧ ∃ fl, (p.toFinset, fl) ∈ blockFT c' := by
  simp only [hitsL, List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true, bne_iff_ne,
    List.any_eq_true, sameL_iff, mem_blockFT]
  constructor
  · rintro ⟨h, q, hq, hs⟩
    exact ⟨h, q.2, q, hq, hs.symm, rfl⟩
  · rintro ⟨h, fl, q, hq, hs, -⟩
    exact ⟨h, q, hq, hs.symm⟩

/-- Interior faces: at most one other cell has the face, and there with the same flag (closed check on lists). -/
def intB : Bool :=
  (List.finRange 8).all fun c => (blockFL c).all fun p =>
    (hitsL c p.1).all fun a => (hitsL c p.1).all fun b => a == b &&
      (blockFL a).any fun q => sameL p.1 q.1 && q.2 == p.2

set_option maxHeartbeats 4000000 in
theorem intB_true : intB = true := by decide +kernel

theorem chk_intF : ∀ c : Fin 8, ∀ p ∈ blockFT c, p.1 ∉ bdF →
    ∃ c' : Fin 8, c' ≠ c ∧ p ∈ blockFT c' ∧
      ∀ c'' : Fin 8, c'' ≠ c → ∀ fl'' : Bool, (p.1, fl'') ∈ blockFT c'' → c'' = c' := by
  intro c p hp hbd
  obtain ⟨l, hl, hpl1, hpl2⟩ := mem_blockFT.mp (show (p.1, p.2) ∈ blockFT c from hp)
  have hB := intB_true
  simp only [intB, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true, sameL_iff] at hB
  have hB' := hB c l hl
  by_cases hh : ∃ a, a ∈ hitsL c l.1
  · obtain ⟨a, ha⟩ := hh
    obtain ⟨-, q, hq, hs, hf⟩ := hB' a ha a ha
    refine ⟨a, (mem_hitsL.mp ha).1, ?_, ?_⟩
    · have e : p = (q.1.toFinset, q.2) := Prod.ext (hpl1.symm.trans hs) (hpl2.symm.trans hf.symm)
      rw [e]
      exact mem_blockFT.mpr ⟨q, hq, rfl, rfl⟩
    · intro c'' hc'' fl'' h''
      have hc : c'' ∈ hitsL c l.1 := mem_hitsL.mpr ⟨hc'', fl'', by rw [hpl1]; exact h''⟩
      exact (hB' c'' hc a ha).1
  · exfalso
    apply hbd
    rw [← hpl1]
    refine mem_bdF (fl := l.2) (mem_blockFT.mpr ⟨l, hl, rfl, rfl⟩) ?_
    intro c' hc' fl' h'
    exact hh ⟨c', mem_hitsL.mpr ⟨hc', fl', h'⟩⟩

/-- Shared faces: three distinct vertices, and the two cell sums on opposite sides (closed check on lists). -/
def geoB : Bool :=
  (List.finRange 8).all fun c => (blockFL c).all fun p =>
    (decide p.1.Nodup && p.1.length == 3) &&
    (List.finRange 8).all fun c' => c' == c || !((blockFL c').any fun q => sameL p.1 q.1 && q.2 == p.2) ||
      p.1.all fun xa => p.1.all fun xb => p.1.all fun xc => xa == xb || xa == xc || xb == xc ||
        decide (EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c) * EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c') < 0)

set_option maxHeartbeats 4000000 in
theorem geoB_true : geoB = true := by decide +kernel

theorem chk_geoF : ∀ c : Fin 8, ∀ c' : Fin 8, c' ≠ c → ∀ p ∈ blockFT c,
    p ∈ blockFT c' → ∀ xa ∈ p.1, ∀ xb ∈ p.1, ∀ xc ∈ p.1, p.1 = {xa, xb, xc} →
      EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c) * EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c') < 0 := by
  intro c c' hne p hp hp' xa hxa xb hxb xc hxc hx
  obtain ⟨l, hl, h1, h2⟩ := mem_blockFT.mp (show (p.1, p.2) ∈ blockFT c from hp)
  obtain ⟨q, hq, g1, g2⟩ := mem_blockFT.mp (show (p.1, p.2) ∈ blockFT c' from hp')
  have hB := geoB_true
  rw [geoB, List.all_eq_true] at hB
  have h := hB c (List.mem_finRange c)
  rw [List.all_eq_true] at h
  have h := h l hl
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hnd, h⟩ := h
  have h := h c' (List.mem_finRange c')
  have hany : ((blockFL c').any fun q => sameL l.1 q.1 && q.2 == l.2) = true :=
    List.any_eq_true.mpr ⟨q, hq, by rw [Bool.and_eq_true, sameL_iff, beq_iff_eq]; exact ⟨h1.trans g1.symm, g2.trans h2.symm⟩⟩
  have hcc : (c' == c) = false := beq_eq_false_iff_ne.mpr hne
  rw [hany, hcc] at h
  simp only [Bool.false_or, Bool.not_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  have hmem : ∀ x, x ∈ p.1 → x ∈ l.1 := fun x hx => by rw [← h1] at hx; exact List.mem_toFinset.mp hx
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hnd
  have hcard : ({xa, xb, xc} : Finset (Fin 27)).card = 3 := by
    rw [← hx, ← h1, List.toFinset_card_of_nodup hnd.1, hnd.2]
  have hab : xa ≠ xb := by
    rintro rfl
    rw [Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)] at hcard
    have := Finset.card_le_two (a := xa) (b := xc)
    omega
  have hac : xa ≠ xc := by
    rintro rfl
    rw [Finset.insert_eq_of_mem (by simp)] at hcard
    have := Finset.card_le_two (a := xb) (b := xa)
    omega
  have hbc : xb ≠ xc := by
    rintro rfl
    rw [Finset.pair_eq_singleton] at hcard
    have := Finset.card_le_two (a := xa) (b := xb)
    omega
  rcases h xa (hmem xa hxa) xb (hmem xb hxb) xc (hmem xc hxc) with ((h | h) | h) | h
  exacts [absurd h hab, absurd h hac, absurd h hbc, h]

theorem chk_int : ∀ c : Fin 8, ∀ p ∈ (blockMesh.cell c).faceTris, p.1 ∉ bdTrisOf blockMesh →
    ∃ c' : Fin 8, c' ≠ c ∧ p ∈ (blockMesh.cell c').faceTris ∧
      ∀ c'' : Fin 8, c'' ≠ c → ∀ fl'' : Bool, (p.1, fl'') ∈ (blockMesh.cell c'').faceTris → c'' = c' := by
  simp only [blockFT_eq, bdF_eq]
  exact chk_intF

theorem chk_geo : ∀ c : Fin 8, ∀ c' : Fin 8, c' ≠ c → ∀ p ∈ (blockMesh.cell c).faceTris,
    p ∈ (blockMesh.cell c').faceTris → ∀ xa ∈ p.1, ∀ xb ∈ p.1, ∀ xc ∈ p.1, p.1 = {xa, xb, xc} →
      EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c) * EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c') < 0 := by
  simp only [blockFT_eq]
  exact chk_geoF

theorem chk_13nb : ∀ c : Fin 8, ∀ p ∈ (blockMesh.cell c).faceTris, (13 : Fin 27) ∈ p.1 →
    p.1 ∉ bdTrisOf blockMesh := by
  simp only [blockFT_eq, bdF_eq]
  exact chk_13nbF

end Ext23
end CFDLean.JST1.Proofs
