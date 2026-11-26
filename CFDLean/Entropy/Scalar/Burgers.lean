import CFDLean.Entropy.Scalar.Periodic
import CFDLean.Schemes.Burgers.Rusanov
import Mathlib.Tactic

/-! Burgers B4-B, B4-S: the square entropy `η(u) = u²/2` of Burgers with entropy variable `v = u`, entropy flux
`q = u³/3` and entropy potential `ψ = u³/6`; the entropy-conservative flux `(a² + ab + b²)/6`; the Rusanov flux is this
flux minus a nonnegative dissipation, so it is entropy stable. The statements about the Rusanov operator are instances
of the generic theorems of `CFDLean.Entropy.Scalar.Periodic`. -/
noncomputable section
open scoped BigOperators

namespace CFDLean.Burgers

open Scalar Periodic

/-- B4-B: square entropy `η(u) = u²/2`: entropy variable `v = η' = u`. -/
def entropyVariable (u : ℝ) : ℝ := u
/-- Entropy flux of the square entropy: `q(u) = u³/3`. -/
def entropyFluxFunction (u : ℝ) : ℝ := u ^ 3 / 3
/-- Entropy potential `ψ = v f - q = u³/6`. -/
def entropyPotential (u : ℝ) : ℝ := u ^ 3 / 6

/-- B4-B: the entropy potential is `v f - q`. -/
theorem entropyPotential_eq (u : ℝ) :
    entropyPotential u = entropyVariable u * physicalFlux u - entropyFluxFunction u := by
  simp only [entropyPotential, entropyVariable, physicalFlux, entropyFluxFunction]
  ring

namespace EntropyConservativeFlux

/-- B4-B: the entropy-conservative two-point flux of Burgers for the square entropy. -/
def eval (a b : ℝ) : ℝ := (a ^ 2 + a * b + b ^ 2) / 6

def numericalFlux : NumericalFlux where
  eval := eval

theorem consistent : Consistent law numericalFlux := by
  intro u
  simp only [numericalFlux, eval, law, physicalFlux]
  ring

/-- B4-B: `(b - a) F_EC(a, b) = b³/6 - a³/6`. -/
theorem entropyConservative : EntropyConservative entropyVariable entropyPotential numericalFlux := by
  intro a b
  simp only [numericalFlux, eval, entropyVariable, entropyPotential]
  ring

end EntropyConservativeFlux

namespace Rusanov

variable {I : Type*}

/-- B4-B: the Burgers Rusanov flux is entropy stable for the square entropy. -/
theorem entropyStable : EntropyStable entropyVariable entropyPotential numericalFlux := by
  intro a b
  simp only [numericalFlux, eval, entropyVariable, entropyPotential, physicalFlux]
  have h1 : |a| ≤ waveSpeed a b := le_max_left _ _
  have h2 : |b| ≤ waveSpeed a b := le_max_right _ _
  have hb : b ≤ waveSpeed a b := (le_abs_self b).trans h2
  have ha : -a ≤ waveSpeed a b := (neg_le_abs a).trans h1
  have hw : 0 ≤ waveSpeed a b := (abs_nonneg a).trans h1
  nlinarith [sq_nonneg (b - a), mul_nonneg (sq_nonneg (b - a)) (by linarith : (0:ℝ) ≤ 6 * waveSpeed a b - (b - a))]

/-- Rusanov equals the entropy-conservative flux minus a dissipation `(a/2 - (uR-uL)/12)(uR - uL)`. -/
theorem eval_eq_entropyConservative_sub (a b : ℝ) :
    eval a b = EntropyConservativeFlux.eval a b - (waveSpeed a b / 2 - (b - a) / 12) * (b - a) := by
  simp only [eval, EntropyConservativeFlux.eval, physicalFlux]
  ring

/-- B4-S: cell entropy inequality of the Burgers Rusanov operator for the square entropy. -/
theorem cell_entropy_inequality (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (u : I → ℝ) (i : I) :
    u i * FiniteVolume.rhs g dx numericalFlux u i ≤
      -(FiniteVolume.entropyFlux g entropyVariable entropyPotential numericalFlux u i -
        FiniteVolume.entropyFlux g entropyVariable entropyPotential numericalFlux u (g.prev i)) / dx :=
  FiniteVolume.cell_entropy_inequality g dx hdx entropyVariable entropyPotential numericalFlux entropyStable u i

/-- B4-S: the Burgers Rusanov operator does not produce energy: `Σ_i u_i L_i(u) ≤ 0`. -/
theorem energy_production_nonpos [Fintype I] (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (u : I → ℝ) :
    ∑ i, u i * FiniteVolume.rhs g dx numericalFlux u i ≤ 0 :=
  FiniteVolume.entropy_production_nonpos g dx hdx entropyVariable entropyPotential numericalFlux entropyStable u

end Rusanov
end CFDLean.Burgers
