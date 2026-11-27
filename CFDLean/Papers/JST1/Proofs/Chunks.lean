import Mathlib.Data.List.Basic

/-! A list passes a Boolean test if each of its chunks does. The closed kernel checks of JST1 use this to split one
large computation into several small declarations: the external kernels of the paranoid comparator need memory in
proportion to the work in one declaration (`docs/LEAN_PERFORMANCE.md`). -/

namespace CFDLean.JST1.Proofs

theorem all_of_chunks {α : Type*} (f : α → Bool) (L : List α) (k m : ℕ) (hl : L.length ≤ k * m)
    (h : ∀ i < m, ((L.drop (k * i)).take k).all f = true) : L.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_mul] at hl; omega)
  have hjk : k * (j / k) + j % k = j := Nat.div_add_mod j k
  have hmod : j % k < k := Nat.mod_lt j hk
  have hi : j / k < m := by
    by_contra hc
    have : k * m ≤ k * (j / k) := Nat.mul_le_mul_left k (by omega)
    omega
  have hc := h (j / k) hi
  rw [List.all_eq_true] at hc
  apply hc
  rw [List.mem_iff_getElem]
  refine ⟨j % k, by simp only [List.length_take, List.length_drop]; omega, ?_⟩
  simp only [List.getElem_take, List.getElem_drop]
  congr 1

end CFDLean.JST1.Proofs
