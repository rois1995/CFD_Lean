import CFDLean.Papers.JST1.Spec.Item10
set_option cleanup.letToHave false -- keep the `let` binders of the statements (as P1-P3)

/-! Statements of item 17 (P4): `prop:sstpde` (lines 411-422, proof 1123-1133), the continuous balance (the pointwise
algebra of `Π` is P2-10.4). The PDE is taken at one point `(t, x)`: derivatives in `t` and along the coordinate lines
`s ↦ x + s e_β`, as `HasDerivAt`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- SST convective flux in direction `β`: `(ρv_β, ρv_α v_β + p δ_αβ, v_β (ρE + p), ρk v_β, ρω v_β)`, with `v` and
`p = (γ-1)(ρE - ½ρ|v|² - ρk)` of the hat state. -/
def sstConvFlux {d : ℕ} (g : Gas) (U : SState d) (β : Fin d) : SState d
  | .flow .mass => U (.flow (.momentum β))
  | .flow (.momentum α) =>
      U (.flow (.momentum α)) * vel (hatState U) β + (if α = β then pressure g (hatState U) else 0)
  | .flow .energy => vel (hatState U) β * (U (.flow .energy) + pressure g (hatState U))
  | .tke => U .tke * vel (hatState U) β
  | .omg => U .omg * vel (hatState U) β

/-- Temperature `T = p / (R ρ)` of the hat state. -/
def sstTemp {d : ℕ} (g : Gas) (R : ℝ) (U : SState d) : ℝ := pressure g (hatState U) / (R * rho (hatState U))

/-- Specific turbulent kinetic energy `k = ρk / ρ`. -/
def sstK {d : ℕ} (U : SState d) : ℝ := U .tke / rho (hatState U)

/-- The viscous and diffusive fluxes of all rows in direction `β` at a point, from the point data `D` (values and
gradients of `v, T, k`, coefficients): mass 0; momentum `τ` with `μ + μ_t`; energy `τ v + κ ∇T` (plus `D_k ∇k` if
`withDk`); `k` row `D_k ∇k`; `ω` row a free value `Fω β` (weight 0). -/
def sstViscFlux {d : ℕ} (D : SSTPoint.Data d) (Fω : Fin d → ℝ) (β : Fin d) : SState d
  | .flow .mass => 0
  | .flow (.momentum α) => SSTPoint.tau D α β
  | .flow .energy => (∑ α, SSTPoint.tau D β α * D.v α) + D.κ * D.GT β + (if D.withDk then D.Dk * D.Gk β else 0)
  | .tke => D.Dk * D.Gk β
  | .omg => Fω β

/-- Source: `P_k - ε` in the `k` row, a free `S_ω` in the `ω` row, 0 in the flow rows. -/
def sstSource {d : ℕ} (Pk ε Sω : ℝ) : SState d
  | .tke => Pk - ε
  | .omg => Sω
  | .flow _ => 0

/-- P4-17.1 (`prop:sstpde`): let `U(t, x)` be admissible at `(t, x)` and differentiable there in `t` and along the
coordinate lines; let `F^v(y)` be viscous fluxes with no mass flux, differentiable along the lines at `x`, equal at
`x` to the SST fluxes of the point data `D` (`v, T = p/(Rρ)` of the hat state at `x`; `∇v, ∇T, ∇k` the derivatives
of the fields `v, T, k` at `x`); and let the PDE `U_t + ∇·F^c(U) = ∇·F^v + S` hold at `(t, x)`. Then with
`G = -v^η·F^v`: `G = θκ∇T` (minus `θ D_k ∇k` if the energy flux has no `D_k ∇k`) at `x`, and
`∂_t η0 + ∇·(v η0 + G) = Π = -θ[μQ + (μ_t Q - P_k) + ε] - κ|∇T|²/(RT²) + r_D`, `θ = 2β = 1/(RT)`,
`r_D = -D_k ∇k·∇θ` (0 with `D_k ∇k` in the energy flux). -/
def P4_17_1 : Prop :=
  ∀ (d : ℕ) (g : Gas) (D : SSTPoint.Data d) (U : ℝ → Vec d → SState d) (Fv : Vec d → Fin d → SState d)
    (t : ℝ) (x : Vec d) (Ut : SState d) (Ux dFc dFv : Fin d → SState d) (Fω : Fin d → ℝ) (Sω : ℝ),
    0 < D.R → SAdmissible g (U t x) →
    HasDerivAt (fun τ => U τ x) Ut t →
    (∀ β, HasDerivAt (fun s : ℝ => U t (x + s • Pi.single β 1)) (Ux β) 0) →
    (∀ β, HasDerivAt (fun s : ℝ => sstConvFlux g (U t (x + s • Pi.single β 1)) β) (dFc β) 0) →
    (∀ β, HasDerivAt (fun s : ℝ => Fv (x + s • Pi.single β 1) β) (dFv β) 0) →
    D.v = vel (hatState (U t x)) → D.T = sstTemp g D.R (U t x) →
    (∀ α β, HasDerivAt (fun s : ℝ => vel (hatState (U t (x + s • Pi.single β 1))) α) (D.Gv α β) 0) →
    (∀ β, HasDerivAt (fun s : ℝ => sstTemp g D.R (U t (x + s • Pi.single β 1))) (D.GT β) 0) →
    (∀ β, HasDerivAt (fun s : ℝ => sstK (U t (x + s • Pi.single β 1))) (D.Gk β) 0) →
    (∀ y β, Fv y β (.flow .mass) = 0) → (∀ β, Fv x β = sstViscFlux D Fω β) →
    Ut + ∑ β, dFc β = ∑ β, dFv β + sstSource D.Pk D.ε Sω →
    let θ := SSTPoint.theta D
    let G : Vec d → Fin d → ℝ := fun y β => -pairF (vEta g (U t y)) (Fv y β)
    (∀ β, G x β = θ * D.κ * D.GT β - (if D.withDk then 0 else θ * D.Dk * D.Gk β)) ∧
    ∃ (a : ℝ) (b : Fin d → ℝ), HasDerivAt (fun τ => eta0 g (U τ x)) a t ∧
      (∀ β, HasDerivAt (fun s : ℝ => vel (hatState (U t (x + s • Pi.single β 1))) β *
          eta0 g (U t (x + s • Pi.single β 1)) + G (x + s • Pi.single β 1) β) (b β) 0) ∧
      a + ∑ β, b β = -θ * (D.μ * SSTPoint.Q D + (D.μt * SSTPoint.Q D - D.Pk) + D.ε) -
        D.κ * Num.dot D.GT D.GT / (D.R * D.T ^ 2) +
        (if D.withDk then 0 else -(D.Dk * Num.dot D.Gk (SSTPoint.Gtheta D)))

end CFDLean.JST1.Spec
