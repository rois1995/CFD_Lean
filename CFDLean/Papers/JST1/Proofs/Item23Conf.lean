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

set_option maxHeartbeats 4000000 in
theorem chk_13nbF : ∀ c : Fin 8, ∀ p ∈ blockFT c, (13 : Fin 27) ∈ p.1 → p.1 ∉ bdF := by
  decide +kernel

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
