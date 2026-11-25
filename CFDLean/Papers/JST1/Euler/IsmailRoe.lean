import CFDLean.Papers.JST1.Euler.State
import CFDLean.Foundations.LogMean
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! The Ismail-Roe entropy-conservative flux (Ismail and Roe 2009), in `d` dimensions, on a vector `y`.
Parameter vector `z = √(ρ/p) (1, v, p)`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1
variable {d : ℕ}

def ismailRoe (g : Gas) (Ua Ub : State d) (y : Vec d) : State d :=
  let z1a := Real.sqrt (rho Ua / pressure g Ua)
  let z1b := Real.sqrt (rho Ub / pressure g Ub)
  let z5a := Real.sqrt (rho Ua * pressure g Ua)
  let z5b := Real.sqrt (rho Ub * pressure g Ub)
  let m1 := (z1a + z1b) / 2
  let m5 := (z5a + z5b) / 2
  let rhoh := m1 * logMean z5a z5b
  let uh : Vec d := fun α => (z1a * vel Ua α + z1b * vel Ub α) / 2 / m1
  let p1 := m5 / m1
  let p2 := (g.γ + 1) / (2 * g.γ) * (logMean z5a z5b / logMean z1a z1b) + (g.γ - 1) / (2 * g.γ) * (m5 / m1)
  let hh := g.γ * p2 / (rhoh * (g.γ - 1)) + Num.dot uh uh / 2
  let un := Num.dot uh y
  fun c => match c with
    | .mass => rhoh * un
    | .momentum α => rhoh * uh α * un + p1 * y α
    | .energy => rhoh * hh * un

end CFDLean.JST1
