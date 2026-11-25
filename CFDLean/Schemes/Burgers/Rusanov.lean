import CFDLean.Physics.Burgers.Flux
import CFDLean.Schemes.Scalar.NumericalFlux

noncomputable section
namespace CFDLean.Burgers

open Scalar

namespace Rusanov

def waveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

def eval (uL uR : ℝ) : ℝ :=
  (physicalFlux uL + physicalFlux uR) / 2 -
    waveSpeed uL uR / 2 * (uR - uL)

def numericalFlux : NumericalFlux where
  eval := eval

theorem consistent : Consistent law numericalFlux := by
  intro u
  simp [numericalFlux, eval, waveSpeed, law, physicalFlux]

end Rusanov
end CFDLean.Burgers
