import CFDLean.Papers.JST1.Euler.State

/-! Boundary fluxes of the Euler equations. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1
variable {d : ℕ}

/-- Pressure (slip-wall) flux on a vector `y`: `(0, p y, 0)`. -/
def pressFlux (g : Gas) (U : State d) (y : Vec d) : State d
  | .momentum α => pressure g U * y α
  | _ => 0

end CFDLean.JST1
