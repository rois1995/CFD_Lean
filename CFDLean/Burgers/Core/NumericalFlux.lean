import CFDLean.Burgers.Core.ConservationLaw

noncomputable section
namespace CFDLean.Burgers.Core

structure NumericalFlux where
  eval : ℝ → ℝ → ℝ

def Consistent (law : ScalarConservationLaw) (numFlux : NumericalFlux) : Prop :=
  ∀ u, numFlux.eval u u = law.flux u

end CFDLean.Burgers.Core
