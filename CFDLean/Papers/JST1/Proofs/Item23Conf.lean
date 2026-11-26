import CFDLean.Papers.JST1.Proofs.Item23Base

/-! Item 23 (P8), part 2: closed kernel checks of the conformity of the block and of the faces at vertex 13. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs
namespace Ext23

open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec Asm11
set_option maxHeartbeats 4000000 in
theorem chk_intF : ∀ c : Fin 8, ∀ p ∈ blockFT c, p.1 ∉ bdF →
    ∃ c' : Fin 8, c' ≠ c ∧ p ∈ blockFT c' ∧
      ∀ c'' : Fin 8, c'' ≠ c → ∀ fl'' : Bool, (p.1, fl'') ∈ blockFT c'' → c'' = c' := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem chk_geoF : ∀ c : Fin 8, ∀ c' : Fin 8, c' ≠ c → ∀ p ∈ blockFT c,
    p ∈ blockFT c' → ∀ xa ∈ p.1, ∀ xb ∈ p.1, ∀ xc ∈ p.1, p.1 = {xa, xb, xc} →
      EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c) * EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c') < 0 := by
  decide +kernel

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
