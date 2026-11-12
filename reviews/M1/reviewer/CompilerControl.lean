import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field

noncomputable section

namespace M1Control

def lengthSquared {d : Nat} (v : Fin d → ℝ) : ℝ :=
  ∑ i, (v i) ^ 2

def productSum {d : Nat} (v w : Fin d → ℝ) : ℝ :=
  ∑ i, v i * w i

end M1Control
