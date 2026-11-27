import CFDLean.Exec.RealScalar
import Mathlib.Data.Rat.Cast.Order

/-! Cast the rational evaluation of the E0 kernel to the reals. -/
namespace ReviewCases.E1

open CFDLean.Exec

scoped instance ratScalar : Scalar ℚ where
  abs := abs
  max := max
  two := 2
  half := 1 / 2
  third := 1 / 3
  twoThirds := 2 / 3
  quarter := 1 / 4
  threeQuarters := 3 / 4

private theorem cast_face (x y : ℚ) :
    ((Scalar.rusanov x y : ℚ) : ℝ) = Scalar.rusanov (x : ℝ) (y : ℝ) := by
  change (((x*x/2 + y*y/2)/2 - max |x| |y| / 2 * (y-x) : ℚ) : ℝ) =
    (((x : ℝ)*x/2 + (y : ℝ)*y/2)/2 - max |(x : ℝ)| |(y : ℝ)| / 2 * (y-x))
  simp [Rat.cast_max]

/-- The entire periodic array, including the wrap at index zero, commutes with the rational cast. -/
theorem cast_step (dx dt : ℚ) (u : Array ℚ) :
    (eulerStepArray dx dt u).map (fun q : ℚ => (q : ℝ)) =
    eulerStepArray (dx : ℝ) (dt : ℝ) (u.map fun q : ℚ => (q : ℝ)) := by
  apply Array.ext (by simp [eulerStepArray])
  intro i hi hj
  simp [eulerStepArray, cast_face]

end ReviewCases.E1
