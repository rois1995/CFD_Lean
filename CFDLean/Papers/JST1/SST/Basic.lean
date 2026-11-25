import CFDLean.Papers.JST1.Euler.State

/-! SST with the turbulent kinetic energy in the total energy (paper Section `sec:turb`): the state
`U = (ρ, ρv, ρE, ρk, ρω)`, the hat state `û = (ρ, ρv, ρE - ρk)`, the coupled entropy `η0 = η ∘ T` and its
variables. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1
variable {d : ℕ}

/-- Components: the flow channels, `ρk` and `ρω`. -/
inductive SChan (d : ℕ) where
  | flow (c : Channel d)
  | tke
  | omg
  deriving DecidableEq, Fintype

abbrev SState (d : ℕ) := SChan d → ℝ

/-- The linear map `T U = û = (ρ, ρv, ρE - ρk)`. -/
def hatState (U : SState d) : State d
  | .energy => U (.flow .energy) - U .tke
  | c => U (.flow c)

/-- Admissible: the hat state is admissible. -/
def SAdmissible (g : Gas) (U : SState d) : Prop := Admissible g (hatState U)

/-- Coupled entropy `η0(U) = -ρ s(û)/(γ-1)`. -/
def eta0 (g : Gas) (U : SState d) : ℝ := entropyFun g (hatState U)

/-- Its variables `v^η = Tᵀ w(û) = (w_0, 2βv, -2β, 2β, 0)`. -/
def vEta (g : Gas) (U : SState d) : SState d
  | .flow c => entropyVars g (hatState U) c
  | .tke => -(entropyVars g (hatState U) .energy)
  | .omg => 0

end CFDLean.JST1
