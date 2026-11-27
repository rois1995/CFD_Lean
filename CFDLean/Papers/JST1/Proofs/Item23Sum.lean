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
/-! One closed check per cell: a check of the external kernels stays small (`docs/LEAN_PERFORMANCE.md`). -/

/-- The nondegeneracy check of the sub-tetrahedra of the cell `c`. -/
def nondegB (c : Fin 8) : Bool := hexTetsF.all fun (t : List (Fin 8)) =>
  sideZ (bZ (blockIdx c (t.getD 0 0))) (bZ (blockIdx c (t.getD 1 0))) (bZ (blockIdx c (t.getD 2 0)))
    (bZ (blockIdx c (t.getD 3 0))) != 0
theorem nondegB_0 : nondegB 0 = true := by decide +kernel
theorem nondegB_1 : nondegB 1 = true := by decide +kernel
theorem nondegB_2 : nondegB 2 = true := by decide +kernel
theorem nondegB_3 : nondegB 3 = true := by decide +kernel
theorem nondegB_4 : nondegB 4 = true := by decide +kernel
theorem nondegB_5 : nondegB 5 = true := by decide +kernel
theorem nondegB_6 : nondegB 6 = true := by decide +kernel
theorem nondegB_7 : nondegB 7 = true := by decide +kernel

theorem chk_nondeg_b : ∀ c : Fin 8, Kind.hex.tets.all (fun (t : List (Fin 8)) =>
    sideZ (bZ (blockIdx c (t.getD 0 0))) (bZ (blockIdx c (t.getD 1 0))) (bZ (blockIdx c (t.getD 2 0)))
      (bZ (blockIdx c (t.getD 3 0))) != 0) = true := by
  rw [hexTets_eq]
  intro c
  fin_cases c
  exacts [nondegB_0, nondegB_1, nondegB_2, nondegB_3, nondegB_4, nondegB_5, nondegB_6, nondegB_7]

/-- The facet sum at vertex 13 of the cell `c`. -/
def sum13 (c : Fin 8) : Z3 := intSB c (fun t o => decide (13 ∈ nodesB c t o))

theorem sum13_0 : sum13 0 = (-2400, -2400, -2400) := by
  simp only [sum13, intSB, hexTets_eq]
  decide +kernel
theorem sum13_1 : sum13 1 = (2400, -2400, -2400) := by
  simp only [sum13, intSB, hexTets_eq]
  decide +kernel
theorem sum13_2 : sum13 2 = (-2400, 2400, -2400) := by
  simp only [sum13, intSB, hexTets_eq]
  decide +kernel
theorem sum13_3 : sum13 3 = (2400, 2400, -2400) := by
  simp only [sum13, intSB, hexTets_eq]
  decide +kernel
theorem sum13_4 : sum13 4 = (-2080, -2240, 2960) := by
  simp only [sum13, intSB, hexTets_eq]
  decide +kernel
theorem sum13_5 : sum13 5 = (2240, -2080, 2960) := by
  simp only [sum13, intSB, hexTets_eq]
  decide +kernel
theorem sum13_6 : sum13 6 = (-2240, 2080, 2960) := by
  simp only [sum13, intSB, hexTets_eq]
  decide +kernel
theorem sum13_7 : sum13 7 = (2080, 2240, 2960) := by
  simp only [sum13, intSB, hexTets_eq]
  decide +kernel

theorem chk_13 : ((List.finRange 8).map fun c => intSB c (fun t o => decide (13 ∈ nodesB c t o))).sum =
    (0, 0, 2240) := by
  change ((List.finRange 8).map sum13).sum = _
  rw [show List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sum13_0, sum13_1, sum13_2, sum13_3,
    sum13_4, sum13_5, sum13_6, sum13_7]
  rfl

end Ext23
end CFDLean.JST1.Proofs
