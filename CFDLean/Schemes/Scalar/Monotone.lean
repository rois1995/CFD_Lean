import CFDLean.Schemes.Scalar.NumericalFlux

/-! Burgers B1-M: the monotone two-point-flux certificate. It is separate from the evaluator and from the consistency
certificate. The name is `MonotoneFlux` so that it does not shadow Mathlib's `Monotone`. -/
noncomputable section
namespace CFDLean.Scalar

/-- A two-point flux is monotone when it is nondecreasing in the left state and nonincreasing in the right state. -/
def MonotoneFlux (numFlux : NumericalFlux) : Prop :=
  (∀ a a' b, a ≤ a' → numFlux.eval a b ≤ numFlux.eval a' b) ∧
  (∀ a b b', b ≤ b' → numFlux.eval a b' ≤ numFlux.eval a b)

end CFDLean.Scalar
