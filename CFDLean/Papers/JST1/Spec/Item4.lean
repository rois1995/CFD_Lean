import CFDLean.Papers.JST1.Viscous.Flux
import CFDLean.Discrete.Mesh
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Frozen statements of item 4: `thm:visc` (lines 319-324, proof 1034-1044). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- P1-4.0: (i) the momentum and energy entropy variables of `(ρ, v, p = ρRT)` are `v/(RT)` and `-1/(RT)`;
(ii) `viscFlux` applied to the gradient of these components (chain rule) is the NS flux. -/
def P1_4_0 : Prop :=
  ∀ (d : ℕ) (g : Gas) (P : ViscParams) (r T : ℝ) (v : Vec d), 0 < r → 0 < T → 0 < P.R →
    (∀ α, entropyVars g (primState g r v (r * P.R * T)) (.momentum α) = v α / (P.R * T)) ∧
    entropyVars g (primState g r v (r * P.R * T)) .energy = -1 / (P.R * T) ∧
    ∀ (Gv : Fin d → Fin d → ℝ) (GT : Vec d) (G : Matrix (Channel d) (Fin d) ℝ),
      (∀ α β, G (.momentum α) β = Gv α β / (P.R * T) - v α * GT β / (P.R * T ^ 2)) →
      (∀ β, G .energy β = GT β / (P.R * T ^ 2)) →
      viscFlux P (entropyVars g (primState g r v (r * P.R * T))) G = nsFlux P v Gv GT

/-- P1-4.1: Galerkin identity `Σ_i w_i·R_i = -Σ_T ω_T |T| G_T : F_T`, for any element fluxes. -/
def P1_4_1 : Prop :=
  ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
    (w : ι → κ → ℝ) (Fl : C → Matrix κ (Fin d) ℝ),
    ∑ i, pairF (w i) (M.galerkinRes Fl i) = -∑ T, M.ω T * M.vol T * frob (M.gradW w T) (Fl T)

/-- P1-4.2: `K(w̄)` is positive semidefinite and linear (d ≤ 3, Stokes, μ, κ ≥ 0, R > 0, w̄_E < 0). -/
def P1_4_2 : Prop :=
  ∀ (d : ℕ) (P : ViscParams) (wb : State d), d ≤ 3 → 0 ≤ P.μ → 0 ≤ P.κ → 0 < P.R → wb .energy < 0 →
    (∀ G, 0 ≤ frob G (viscFlux P wb G)) ∧ IsLinearMap ℝ (viscFlux P wb)

/-- P1-4.3 (`thm:visc`): the viscous operator with one frozen `K(w̄_T)` per cell dissipates entropy. -/
def P1_4_3 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d) (P : ViscParams)
    (w : ι → State d), M.Valid → d ≤ 3 → 0 ≤ P.μ → 0 ≤ P.κ → 0 < P.R → (∀ i, w i .energy < 0) →
    let wbar : C → State d := fun T => (1 / ((d : ℝ) + 1)) • ∑ a, w (M.vert T a)
    let Fl : C → Matrix (Channel d) (Fin d) ℝ := fun T => viscFlux P (wbar T) (M.gradW w T)
    (∀ T, wbar T .energy < 0) ∧
    ∑ i, pairF (w i) (M.galerkinRes Fl i) = -∑ T, M.ω T * M.vol T * frob (M.gradW w T) (Fl T) ∧
    ∑ i, pairF (w i) (M.galerkinRes Fl i) ≤ 0

/-- P1-4.3b: admissible states have `w_E < 0`. -/
def P1_4_3b : Prop :=
  ∀ (d : ℕ) (g : Gas) (U : State d), Admissible g U → entropyVars g U .energy < 0

/-- P1-4.4: symmetry `G : K H = H : K G`. -/
def P1_4_4 : Prop :=
  ∀ (d : ℕ) (P : ViscParams) (wb : State d) (G H : Matrix (Channel d) (Fin d) ℝ), wb .energy ≠ 0 →
    frob G (viscFlux P wb H) = frob H (viscFlux P wb G)

end CFDLean.JST1.Spec
