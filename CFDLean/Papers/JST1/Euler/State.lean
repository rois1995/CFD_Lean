import CFDLean.Foundations.Basic

/-! Ideal-gas Euler states in `d` dimensions, the entropy of paper 1 (`U = -ρ s/(γ-1)`), its variables, the
enthalpy state `ũ = (ρ, ρv, ρH)` and the Euler flux. Exact reals; definitions are total. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1

/-- Conserved components; separate tags (pattern of `SU2_Lean/SU2/Spec.lean`). -/
inductive Channel (d : ℕ) where
  | mass
  | momentum (α : Fin d)
  | energy
  deriving DecidableEq, Fintype

abbrev State (d : ℕ) := Channel d → ℝ

structure Gas where
  γ : ℝ
  one_lt_γ : 1 < γ

variable {d : ℕ}

def rho (U : State d) : ℝ := U .mass
def mom (U : State d) : Vec d := fun α => U (.momentum α)
def energy (U : State d) : ℝ := U .energy
def vel (U : State d) : Vec d := fun α => mom U α / rho U

def pressure (g : Gas) (U : State d) : ℝ := (g.γ - 1) * (energy U - Num.dot (mom U) (mom U) / (2 * rho U))

/-- Admissible: `ρ > 0`, `p > 0`. -/
def Admissible (g : Gas) (U : State d) : Prop := 0 < rho U ∧ 0 < pressure g U

/-- Physical entropy `s = ln(p ρ^{-γ})`. -/
def physEntropy (g : Gas) (U : State d) : ℝ := Real.log (pressure g U) - g.γ * Real.log (rho U)

/-- Entropy function `U = -ρ s/(γ-1)`. -/
def entropyFun (g : Gas) (U : State d) : ℝ := -(rho U) * physEntropy g U / (g.γ - 1)

/-- Entropy variables `w = ((γ - s)/(γ-1) - ρ|v|²/(2p), ρv/p, -ρ/p)`. -/
def entropyVars (g : Gas) (U : State d) : State d
  | .mass => (g.γ - physEntropy g U) / (g.γ - 1) - rho U * Num.dot (vel U) (vel U) / (2 * pressure g U)
  | .momentum α => rho U * vel U α / pressure g U
  | .energy => -(rho U) / pressure g U

/-- Flux potential `ψ = ρv`. -/
def fluxPot (U : State d) : Vec d := mom U

/-- Unit vector of the energy component. -/
def eE : State d
  | .energy => 1
  | _ => 0

/-- Enthalpy state `ũ = u + p e_E = (ρ, ρv, ρH)`. -/
def enthalpyState (g : Gas) (U : State d) : State d := U + pressure g U • eE

/-- Euler flux on a vector `y`: `F(u)·y`. -/
def physFlux (g : Gas) (U : State d) (y : Vec d) : State d
  | .mass => Num.dot (mom U) y
  | .momentum α => mom U α * Num.dot (vel U) y + pressure g U * y α
  | .energy => (energy U + pressure g U) * Num.dot (vel U) y

/-- Conservative state from primitive variables `(ρ, v, p)`. -/
def primState (g : Gas) (r : ℝ) (v : Vec d) (p : ℝ) : State d
  | .mass => r
  | .momentum α => r * v α
  | .energy => p / (g.γ - 1) + r * Num.dot v v / 2

/-- Bounds of `lem:eps2`: `λ_γ, Λ_γ = (γ + 1 ∓ √(γ(γ-1)))/2`. -/
def lamLow (γ : ℝ) : ℝ := (γ + 1 - Real.sqrt (γ * (γ - 1))) / 2
def lamHigh (γ : ℝ) : ℝ := (γ + 1 + Real.sqrt (γ * (γ - 1))) / 2

/-- Thermodynamic parts of the forms `q`, `q̃` (paper lines 264-265, without the factor `ρ/(γ-1)`). -/
def thermoQ (γ a b : ℝ) : ℝ := γ * a ^ 2 - 2 * a * b + b ^ 2
def thermoQt (γ a b : ℝ) : ℝ := γ * a ^ 2 - (γ + 1) * a * b + γ * b ^ 2

end CFDLean.JST1
