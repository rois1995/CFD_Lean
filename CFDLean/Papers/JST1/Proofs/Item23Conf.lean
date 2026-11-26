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

-- every face at vertex 13 is also a face of a second cell (closed check without `bdF`)
set_option maxHeartbeats 4000000 in
theorem chk_13nbF : ∀ c : Fin 8, ∀ p ∈ blockFT c, (13 : Fin 27) ∈ p.1 →
    ∃ c' : Fin 8, c' ≠ c ∧ ((p.1, true) ∈ blockFT c' ∨ (p.1, false) ∈ blockFT c') := by
  decide +kernel

-- a face of two different cells is not a boundary face
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
  intro c p hp h13
  obtain ⟨c', hc, h | h⟩ := chk_13nbF c p hp h13
  exacts [not_bdF hc hp h, not_bdF hc hp h]

end Ext23
end CFDLean.JST1.Proofs
