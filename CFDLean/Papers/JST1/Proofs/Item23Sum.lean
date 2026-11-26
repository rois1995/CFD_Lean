import CFDLean.Papers.JST1.Proofs.Item23Base

/-! Item 23 (P8), part 3: closed kernel checks of the nondegeneracy of all sub-tetrahedra of the block and of the
facet sum at vertex 13. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs
namespace Ext23

open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec Asm11
set_option maxHeartbeats 4000000 in
theorem chk_nondeg_b : ∀ c : Fin 8, Kind.hex.tets.all (fun (t : List (Fin 8)) =>
    sideZ (bZ (blockIdx c (t.getD 0 0))) (bZ (blockIdx c (t.getD 1 0))) (bZ (blockIdx c (t.getD 2 0)))
      (bZ (blockIdx c (t.getD 3 0))) != 0) = true := by
  rw [hexTets_eq]
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem chk_13 : ((List.finRange 8).map fun c => intSB c (fun t o => decide (13 ∈ nodesB c t o))).sum =
    (0, 0, 2240) := by
  simp only [intSB, hexTets_eq]
  decide +kernel

end Ext23
end CFDLean.JST1.Proofs
