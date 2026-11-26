import CFDLean.Discrete.Periodic.Grid
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.NormNum

noncomputable section
namespace CFDLean.FV1D

variable {S I : Type*} [AddCommGroup S] [Module ℝ S]

/-- Right-oriented Rusanov flux. The speed scales the jump in conserved state. -/
def face (F : S → S) (a : S → S → ℝ) (L R : S) : S :=
  (1 / 2 : ℝ) • (F L + F R) - (a L R / 2) • (R - L)

theorem face_self (F : S → S) (a : S → S → ℝ) (C : S) : face F a C C = F C := by
  simp only [face, sub_self, smul_zero, sub_zero, smul_add, ← add_smul]
  norm_num

/-- Both right-face values use the old cell averages, including at the periodic seam. -/
def step (g : Periodic.Grid I) (F : S → S) (a : S → S → ℝ) (dx dt : ℝ) (U : I → S) (i : I) : S :=
  let h := fun j => face F a (U j) (U (g.next j))
  U i - (dt / dx) • (h i - h (g.prev i))

theorem step_constant (g : Periodic.Grid I) (F : S → S) (a : S → S → ℝ) (dx dt : ℝ) (C : S) :
    step g F a dx dt (fun _ => C) = fun _ => C := by
  funext i
  simp [step, face_self]

theorem step_sum [Fintype I] (g : Periodic.Grid I) (F : S → S) (a : S → S → ℝ)
    (dx dt : ℝ) (U : I → S) : ∑ i, step g F a dx dt U i = ∑ i, U i := by
  let h := fun j => face F a (U j) (U (g.next j))
  have reindex : ∑ i, h (g.prev i) = ∑ i, h i :=
    Fintype.sum_equiv g.next.symm _ _ (fun _ => rfl)
  change ∑ i, (U i - (dt / dx) • (h i - h (g.prev i))) = _
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_sub_distrib, reindex]
  simp

end CFDLean.FV1D
