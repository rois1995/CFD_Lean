import CFDLean.Papers.JST1.Spec.Item2
import CFDLean.Papers.JST1.Spec.Item4
import CFDLean.Papers.JST1.Spec.Item5
import CFDLean.Discrete.Mesh
import CFDLean.Discrete.Galerkin

noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

theorem grad_sum {d : ℕ} (T : Simplex d) : ∑ a, T.grad a = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [Simplex.grad, Fin.cases_zero, Fin.cases_succ]
  exact neg_add_cancel _

section
variable {ι C X : Type} [Fintype ι] [DecidableEq ι] [Fintype C] [AddCommMonoid X] {d : ℕ}
  (M : WMesh ι C d)

/-- Summing over the vertex of a single indicator. -/
theorem sum_single (f : C → Fin (d + 1) → X) :
    (∑ i, ∑ T, ∑ a, if M.vert T a = i then f T a else 0) = ∑ T, ∑ a, f T a := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp
end

theorem p1_2_3 : Spec.P1_2_3 := CFDLean.Num.WMesh.nW_row_sum

theorem p1_4_1 : Spec.P1_4_1 := CFDLean.Num.WMesh.galerkin_identity

theorem p1_5_5 : Spec.P1_5_5 := CFDLean.Num.WMesh.fvRes_eq_galerkinRes

end CFDLean.JST1.Proofs
