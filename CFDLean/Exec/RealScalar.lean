import CFDLean.Exec.Kernel
import Mathlib.Basic.Real.Basic

/-! Burgers E0: the real-number instance of the kernel arithmetic. With this instance the kernel is a (noncomputable)
function on arrays of real numbers; the refinement theorems are about that function. This module and the kernel are
the trusted inputs of the E0 statements. -/
noncomputable section
namespace CFDLean.Exec

/-- The specification arithmetic: every field is the corresponding real operation or literal. -/
noncomputable instance instScalarReal : Scalar ℝ where
  toAdd := inferInstance
  toSub := inferInstance
  toMul := inferInstance
  toDiv := inferInstance
  toNeg := inferInstance
  toZero := inferInstance
  abs x := |x|
  max := max
  two := 2
  half := 1 / 2
  third := 1 / 3
  twoThirds := 2 / 3
  quarter := 1 / 4
  threeQuarters := 3 / 4

end CFDLean.Exec
