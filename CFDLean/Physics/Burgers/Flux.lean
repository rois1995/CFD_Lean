import CFDLean.Physics.Scalar.ConservationLaw

noncomputable section
namespace CFDLean.Burgers

open Core

def physicalFlux (u : ℝ) : ℝ := u ^ 2 / 2

def law : ScalarConservationLaw where
  flux := physicalFlux

end CFDLean.Burgers
