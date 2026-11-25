import CFDLean.Papers.JST1.Spec.Item12

/-! Proofs of item 12 (P3), combinatorial part: slivers among the hexahedron splits, the weight bound, and the
neighbour-fan subset. -/
noncomputable section
open scoped BigOperators
namespace CFDLean.JST1.Proofs

/-- Closed computation on the hexahedron splits, checked by the kernel. -/
theorem p3_12_1 : Spec.P3_12_1 := by
  unfold Spec.P3_12_1
  decide

theorem p3_12_3 : Spec.P3_12_3 := by
  intro σ _ ω q t hω hq ht
  calc q t / 16 = (1 / 16) * q t := by ring
    _ ≤ ω t * q t := mul_le_mul_of_nonneg_right ht (hq t)
    _ ≤ ∑ s, ω s * q s :=
        Finset.single_le_sum (f := fun s => ω s * q s) (fun s _ => mul_nonneg (hω s) (hq s))
          (Finset.mem_univ t)

/-- Closed computation on the neighbour-fan splits, checked by the kernel. -/
theorem p3_12_4 : Spec.P3_12_4 := by
  unfold Spec.P3_12_4
  decide

end CFDLean.JST1.Proofs
