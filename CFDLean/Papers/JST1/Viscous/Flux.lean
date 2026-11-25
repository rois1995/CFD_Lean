import CFDLean.Papers.JST1.Euler.State
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Navier-Stokes viscous and heat fluxes written in entropy variables: `K(w̄) G` for a frozen state `w̄` and a
gradient `G` of the entropy variables (rows: components, columns: directions). Stokes hypothesis. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1
variable {d : ℕ}

structure ViscParams where
  R : ℝ
  μ : ℝ
  κ : ℝ

/-- `θ = -w_E = 1/(RT)`, `v = w_m/θ`, `∂v = (G_m - v ⊗ G_θ)/θ`, `∂T = -G_θ/(R θ²)`, `G_θ = -G_E`;
`τ = μ(∂v + ∂vᵀ) - (2/3) μ (div v) I`; flux `(0, τ, τ v + κ ∂T)`. Entry `(α, β)` of `Dv` is `∂_β v_α`. -/
def viscFlux (P : ViscParams) (wb : State d) (G : Matrix (Channel d) (Fin d) ℝ) :
    Matrix (Channel d) (Fin d) ℝ :=
  let θ := -wb .energy
  let v : Vec d := fun α => wb (.momentum α) / θ
  let Gθ : Vec d := fun β => -G .energy β
  let Dv : Fin d → Fin d → ℝ := fun α β => (G (.momentum α) β - v α * Gθ β) / θ
  let DT : Vec d := fun β => -Gθ β / (P.R * θ ^ 2)
  let divv := ∑ α, Dv α α
  let τ : Fin d → Fin d → ℝ := fun α β =>
    P.μ * (Dv α β + Dv β α) - (2 / 3) * P.μ * divv * (if α = β then 1 else 0)
  fun c β => match c with
    | .mass => 0
    | .momentum α => τ α β
    | .energy => ∑ α, τ β α * v α + P.κ * DT β

/-- The NS viscous and heat flux from primitive gradients: `Gv α β = ∂_β v_α`, `GT β = ∂_β T`. -/
def nsFlux (P : ViscParams) (v : Vec d) (Gv : Fin d → Fin d → ℝ) (GT : Vec d) :
    Matrix (Channel d) (Fin d) ℝ :=
  let divv := ∑ α, Gv α α
  let τ : Fin d → Fin d → ℝ := fun α β =>
    P.μ * (Gv α β + Gv β α) - (2 / 3) * P.μ * divv * (if α = β then 1 else 0)
  fun c β => match c with
    | .mass => 0
    | .momentum α => τ α β
    | .energy => ∑ α, τ β α * v α + P.κ * GT β

end CFDLean.JST1
