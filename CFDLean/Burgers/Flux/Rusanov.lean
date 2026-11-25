import CFDLean.Burgers.Core.NumericalFlux
import Mathlib.Data.Real.Basic

noncomputable section
namespace CFDLean.Burgers

open Core

def physicalFlux (u : ℝ) : ℝ := u ^ 2 / 2

def law : ScalarConservationLaw where
  flux := physicalFlux

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
