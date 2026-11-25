import CFDLean.Papers.JST1.Viscous.Wall
import CFDLean.Papers.JST1.Viscous.Flux

/-! Statements of item 9 (P2): `thm:wall` (lines 336-346, proof 1067-1090), on one simplex `T`. `K` is the frozen
viscous map `K(w̄_T)` (linear, symmetric, positive semidefinite: P1-4.2, P1-4.4), `P` the constant orthogonal
projector of the wall conditions, `gw` their data (`P gw = gw`). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec
open CFDLean.JST1.Wall

/-- Hypotheses on `K`, `P`, `gw`. -/
def WallHyp {κ : Type} [Fintype κ] {d : ℕ} (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ) (P : Matrix κ κ ℝ)
    (gw : κ → ℝ) : Prop :=
  IsLinearMap ℝ K ∧ (∀ G H, frob G (K H) = frob H (K G)) ∧ (∀ G, 0 ≤ frob G (K G)) ∧
    P.transpose = P ∧ P * P = P ∧ P.mulVec gw = gw

/-- P2-9.0 (balance): the viscous and wall terms of the element produce `-D^gal_T + Π^w_T` plus the discrete wall
flux `Σ_f (A_f/d) Σ_{a∈f} g·F̂_a`. -/
def P2_9_0 : Prop :=
  ∀ (κ : Type) [Fintype κ] (d : ℕ) (T : Simplex d) (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ)
    (P : Matrix κ κ ℝ) (gw : κ → ℝ) (walls : Finset (Fin (d + 1))) (c : ℝ) (w : Fin (d + 1) → κ → ℝ),
    WallHyp K P gw →
    ∑ b, pairF (w b) (Rvisc T K w b + Rwall T K P gw walls c w b) =
      -Dgal T K w + PiW T K P gw walls c w +
        ∑ o ∈ walls, area T o / d * ∑ a ∈ Finset.univ.erase o, pairF gw (Fhat T K P gw walls c w o a)

/-- P2-9.1: `Π^w_T ≤ D^gal_T / c` for `c > 0` (no aspect-ratio constant); for `c ≥ 1`,
`D^gal_T - Π^w_T ≥ (1 - 1/c) D^gal_T ≥ 0`. -/
def P2_9_1 : Prop :=
  ∀ (κ : Type) [Fintype κ] (d : ℕ) (T : Simplex d) (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ)
    (P : Matrix κ κ ℝ) (gw : κ → ℝ) (walls : Finset (Fin (d + 1))) (c : ℝ) (w : Fin (d + 1) → κ → ℝ),
    WallHyp K P gw → 1 ≤ d → T.Nondeg → 0 < c →
    PiW T K P gw walls c w ≤ Dgal T K w / c ∧
    (1 ≤ c → (1 - 1 / c) * Dgal T K w ≤ Dgal T K w - PiW T K P gw walls c w ∧ 0 ≤ (1 - 1 / c) * Dgal T K w)

/-- P2-9.2 (`c ≥ 1` is sharp for one wall element): if `c < 1` and `|e ⊗ N_f|²_K > 0` for some `e = P e`, there are
nodal values with `D^gal_T - Π^w_T < 0`. -/
def P2_9_2 : Prop :=
  ∀ (κ : Type) [Fintype κ] (d : ℕ) (T : Simplex d) (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ)
    (P : Matrix κ κ ℝ) (gw : κ → ℝ) (o : Fin (d + 1)) (c : ℝ) (e : κ → ℝ),
    WallHyp K P gw → 1 ≤ d → T.Nondeg → 0 < c → c < 1 → P.mulVec e = e →
    0 < frob (outerK e (normal T o)) (K (outerK e (normal T o))) →
    ∃ w : Fin (d + 1) → κ → ℝ, Dgal T K w - PiW T K P gw {o} c w < 0

/-- Projector on the momentum components (no-slip, adiabatic). -/
def momProj (d : ℕ) : Matrix (Channel d) (Channel d) ℝ :=
  Matrix.diagonal fun c => match c with
    | .momentum _ => 1
    | _ => 0

/-- P2-9.3: the Navier-Stokes `K(w̄)` with `μ > 0` and the momentum projector meet the hypotheses of P2-9.2 for
every nonzero normal (so the sharpness example is a real one). -/
def P2_9_3 : Prop :=
  ∀ (d : ℕ) (Pv : ViscParams) (wb : State d) (N : Vec d), 1 ≤ d → d ≤ 3 → 0 < Pv.μ → 0 ≤ Pv.κ → 0 < Pv.R →
    wb .energy < 0 → N ≠ 0 →
    WallHyp (viscFlux Pv wb) (momProj d) 0 ∧
    ∃ e : State d, (momProj d).mulVec e = e ∧ 0 < frob (outerK e N) (viscFlux Pv wb (outerK e N))

/-- P2-9.4: the no-slip and isothermal conditions are linear and constant in entropy variables:
`v = 0 ⟺ w_m = 0` and `T = T_w ⟺ w_E = -1/(R T_w)`. -/
def P2_9_4 : Prop :=
  ∀ (d : ℕ) (g : Gas) (R r T Tw : ℝ) (v : Vec d), 0 < R → 0 < r → 0 < T → 0 < Tw →
    ((v = 0) ↔ ∀ α, entropyVars g (primState g r v (r * R * T)) (.momentum α) = 0) ∧
    ((T = Tw) ↔ entropyVars g (primState g r v (r * R * T)) .energy = -1 / (R * Tw))

end CFDLean.JST1.Spec
