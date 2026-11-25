import CFDLean.Core.PhysicalFlux
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases

noncomputable section
namespace CFDLean.Coordinates
open scoped BigOperators

abbrev StateCoordinates := Fin 5 → ℝ

def encode (U : Conservative 3) : StateCoordinates :=
  ![U.density, U.momentum 0, U.momentum 1, U.momentum 2, U.energy]

def decode (x : StateCoordinates) : Conservative 3 :=
  ⟨x 0, ![x 1, x 2, x 3], x 4⟩

theorem decode_encode (U : Conservative 3) : decode (encode U) = U := by
  cases U with
  | mk ρ m E =>
    have hm : ![m 0, m 1, m 2] = m := by
      funext i
      fin_cases i <;> rfl
    change Conservative.mk ρ ![m 0, m 1, m 2] E = Conservative.mk ρ m E
    rw [hm]

theorem encode_decode (x : StateCoordinates) : encode (decode x) = x := by
  funext i
  fin_cases i <;> rfl

theorem squareSum_three (v : Vector 3) :
    squareSum v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [squareSum, Fin.sum_univ_succ, add_assoc]

theorem dot_three (v w : Vector 3) :
    dot v w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
  simp [dot, Fin.sum_univ_succ, add_assoc]

/-- Euclidean face area; the default finite-function norm is not used. -/
def area (S : Vector 3) : ℝ := Real.sqrt (squareSum S)

def unitNormal (S : Vector 3) : Vector 3 := fun i => S i / area S

theorem squareSum_nonneg (S : Vector 3) : 0 ≤ squareSum S := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (S i))

theorem squareSum_pos (S : Vector 3) (hS : S ≠ 0) : 0 < squareSum S := by
  classical
  have h : ¬ ∀ i, S i = 0 := fun h => hS (funext h)
  obtain ⟨i, hi⟩ := not_forall.mp h
  exact Finset.sum_pos' (fun j _ => sq_nonneg (S j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem area_pos (S : Vector 3) (hS : S ≠ 0) : 0 < area S :=
  Real.sqrt_pos.mpr (squareSum_pos S hS)

theorem unitNormal_dot_self (S : Vector 3) (hS : S ≠ 0) :
    dot (unitNormal S) (unitNormal S) = 1 := by
  have hdot : ∀ v : Vector 3, dot v v = squareSum v := by
    intro v
    simp [dot, squareSum, pow_two]
  rw [hdot]
  change squareSum (fun i => S i / area S) = 1
  rw [squareSum_div]
  rw [show area S ^ 2 = squareSum S from Real.sq_sqrt (squareSum_nonneg S)]
  exact div_self (ne_of_gt (squareSum_pos S hS))

theorem reconstruct_area (S : Vector 3) (hS : S ≠ 0) :
    S = fun i => area S * unitNormal S i := by
  funext i
  exact (mul_div_cancel₀ (S i) (ne_of_gt (area_pos S hS))).symm

theorem area_zero : area (0 : Vector 3) = 0 := by
  simp [area, squareSum]

theorem area_oblique : area (![2, 3, 0] : Vector 3) = Real.sqrt 13 := by
  rw [area, squareSum_three]
  change Real.sqrt ((2 : ℝ) ^ 2 + 3 ^ 2 + 0 ^ 2) = Real.sqrt 13
  norm_num

end CFDLean.Coordinates
