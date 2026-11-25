import CFDLean.Papers.JST1.Euler.State

/-! Pointwise entropy production of the SST system (`prop:sstpde`, proof lines 1123-1133), from the values and
gradients at one point. `θ = 2β = 1/(RT)`. `Gv α β = ∂_β v_α`, `GT = ∇T`, `Gk = ∇k`. The viscous fluxes:
momentum `τ` with `μ + μ_t`, energy `τ v + κ ∇T` (plus `D_k ∇k` if `withDk`), `k` row `D_k ∇k`; the `ω` row has
weight 0 and the mass row has no viscous flux. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1
namespace SSTPoint
variable {d : ℕ}

structure Data (d : ℕ) where
  R : ℝ
  T : ℝ
  v : Vec d
  Gv : Fin d → Fin d → ℝ
  GT : Vec d
  Gk : Vec d
  μ : ℝ
  μt : ℝ
  κ : ℝ
  Dk : ℝ
  Pk : ℝ
  ε : ℝ
  withDk : Bool

def theta (D : Data d) : ℝ := 1 / (D.R * D.T)
def Gtheta (D : Data d) : Vec d := fun β => -D.GT β / (D.R * D.T ^ 2)
def divv (D : Data d) : ℝ := ∑ α, D.Gv α α
def tau (D : Data d) (α β : Fin d) : ℝ :=
  (D.μ + D.μt) * (D.Gv α β + D.Gv β α) - (2 / 3) * (D.μ + D.μt) * divv D * (if α = β then 1 else 0)
/-- `S:S` with `S` the symmetric part of `∇v`. -/
def SS (D : Data d) : ℝ := ∑ α, ∑ β, ((D.Gv α β + D.Gv β α) / 2) ^ 2
/-- `Q = 2 S:S - (2/3)(div v)²`. -/
def Q (D : Data d) : ℝ := 2 * SS D - (2 / 3) * divv D ^ 2

/-- `Π = -∇v^η : F^v + v^η · S` with `v^η = (w_0, θ v, -θ, θ, 0)` and the source `P_k - ε` in the `k` row. -/
def Pi (D : Data d) : ℝ :=
  -((∑ α, ∑ β, (theta D * D.Gv α β + D.v α * Gtheta D β) * tau D α β) +
      (∑ β, (-Gtheta D β) * ((∑ α, tau D β α * D.v α) + D.κ * D.GT β +
        (if D.withDk then D.Dk * D.Gk β else 0))) +
      (∑ β, Gtheta D β * (D.Dk * D.Gk β))) +
    theta D * (D.Pk - D.ε)

end SSTPoint
end CFDLean.JST1
