import CFDLean.Physics.Scalar.ConservationLaw

noncomputable section
namespace CFDLean.Burgers

open Scalar

def physicalFlux (u : ℝ) : ℝ := u ^ 2 / 2

def law : ConservationLaw where
  flux := physicalFlux

end CFDLean.Burgers
