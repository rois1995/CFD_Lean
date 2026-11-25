import CFDLean.Physics.Scalar.ConservationLaw

noncomputable section
namespace CFDLean.Scalar

structure NumericalFlux where
  eval : ℝ → ℝ → ℝ

def Consistent (law : ConservationLaw) (numFlux : NumericalFlux) : Prop :=
  ∀ u, numFlux.eval u u = law.flux u

end CFDLean.Scalar
