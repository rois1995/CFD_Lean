import CFDLean.Papers.JST1.Proofs.DissGeom
import CFDLean.Papers.JST1.Spec.Item7
import CFDLean.Discrete.Mesh

/-! Proofs of item 7 (P2): `lem:dissgeom`(d) and `prop:consistency`(c), first part. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs

namespace Dg7
open DissGeom

section Vec
variable {d : ℕ}

theorem frob_add (A B H : Matrix (Fin d) (Fin d) ℝ) : frob (A + B) H = frob A H + frob B H := by
  simp only [frob, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

end Vec

section Mesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

theorem ne_nonneg (hM : M.Valid) (i k : ι) : 0 ≤ Num.dot (M.n i k) (M.e i k) := by
  by_cases hk : i = k
  · subst hk; rw [e_self, dot_zero_r]
  · rw [n_dot_e M hM i k hk]; linarith [mu_nonneg M hM i k]

end Mesh
end Dg7

open Dg7 DissGeom

theorem p2_7_1 : Spec.P2_7_1 := CFDLean.Num.quadratic_edge_expansion

theorem p2_7_2 : Spec.P2_7_2 := CFDLean.Num.dissTensor_loewner

theorem p2_7_3 : Spec.P2_7_3 := CFDLean.Num.WMesh.dissTensor_trace

theorem p2_7_4 : Spec.P2_7_4 := by
  intro ι C _ _ _ d M vb cb σmax hM hσ
  have hterm : ∀ i k, lamHat (vb i k) (cb i k) (M.e i k) (M.n i k) * len (M.e i k) ≤
      σmax * (len (M.nu i k) * len (M.e i k)) := by
    intro i k
    by_cases he : M.e i k = 0
    · rw [he, len_zero, mul_zero, mul_zero, mul_zero]
    · have hee : 0 < Num.dot (M.e i k) (M.e i k) :=
        lt_of_le_of_ne (dot_self_nonneg _) (fun h0 => he (eq_zero_of_dot_self _ h0.symm))
      have hle : 0 < len (M.e i k) := Real.sqrt_pos.2 hee
      set t := Num.dot (M.n i k) (M.e i k) / Num.dot (M.e i k) (M.e i k) with ht
      have ht0 : 0 ≤ t := div_nonneg (Dg7.ne_nonneg M hM i k) hee.le
      have hnu : M.nu i k = t • M.e i k := rfl
      have hlen : len (M.nu i k) = t * len (M.e i k) := by rw [hnu, len_smul', abs_of_nonneg ht0]
      have hdot : |Num.dot (vb i k) (M.nu i k)| =
          |Num.dot (vb i k) (WMesh.unit (M.e i k))| * len (M.nu i k) := by
        rw [hlen, hnu, dot_smul_r, WMesh.unit, dot_smul_r, abs_mul, abs_mul,
          abs_of_nonneg ht0, abs_of_pos (by positivity : (0 : ℝ) < 1 / len (M.e i k))]
        field_simp
      unfold lamHat
      rw [show WMesh.nuOf (M.n i k) (M.e i k) = M.nu i k from rfl, hdot]
      have := (hσ i k).2
      have h0 := len_nonneg (M.nu i k)
      nlinarith [mul_nonneg h0 hle.le]
  have hsum := (p1_5_4 ι C d M hM).2.1
  calc ∑ i, ∑ k, lamHat (vb i k) (cb i k) (M.e i k) (M.n i k) * len (M.e i k)
      ≤ ∑ i, ∑ k, σmax * (len (M.nu i k) * len (M.e i k)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hterm i k
    _ = 2 * d * σmax * M.volΩ := by
        simp only [← Finset.mul_sum]
        rw [hsum]; ring

end CFDLean.JST1.Proofs
