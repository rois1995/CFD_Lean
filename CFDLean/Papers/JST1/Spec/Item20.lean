import CFDLean.Papers.JST1.Euler.State
import CFDLean.Physics.Euler.PhysicalFlux
set_option cleanup.letToHave false -- keep the `let` binders of the statements (as P1-P4)

/-! Statements of item 20 (P5): the paper's Euler definitions (`CFDLean.JST1`, `Euler/State.lean`) against the M1
Euler physics (`CFDLean.Conservative`, `CFDLean.Primitive`, `CFDLean.physicalFlux`). Bridge only: no frozen definition
changes. M1 has no entropy; P5-20.4 writes the paper's entropy and entropy variables in M1's primitive variables. The
differences are listed in `specifications/JST1/P5.md`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

variable {d : ℕ}

/-- M1 conservative state -> paper state (component by component). -/
def toState (U : CFDLean.Conservative d) : State d
  | .mass => U.density
  | .momentum α => U.momentum α
  | .energy => U.energy

/-- Paper state -> M1 conservative state. -/
def ofState (U : State d) : CFDLean.Conservative d := ⟨rho U, mom U, energy U⟩

/-- P5-20.1 (state map): `toState` and `ofState` are inverse bijections, and they match the components
(`ρ`, `ρv`, `ρE`). -/
def P5_20_1 : Prop :=
  ∀ d : ℕ,
    (∀ U : CFDLean.Conservative d, ofState (toState U) = U) ∧
    (∀ U : State d, toState (ofState U) = U) ∧
    (∀ U : CFDLean.Conservative d,
      rho (toState U) = U.density ∧ mom (toState U) = U.momentum ∧ energy (toState U) = U.energy)

/-- P5-20.2 (pressure, admissibility, primitive variables): for every gas, the paper's pressure, admissibility,
velocity and primitive-to-conservative map are M1's (with M1's `γ = g.γ`). -/
def P5_20_2 : Prop :=
  ∀ (d : ℕ) (g : Gas),
    (∀ U : CFDLean.Conservative d, pressure g (toState U) = U.pressure g.γ) ∧
    (∀ U : CFDLean.Conservative d, Admissible g (toState U) ↔ U.Admissible g.γ) ∧
    (∀ U : CFDLean.Conservative d, vel (toState U) = (U.toPrimitive g.γ).velocity) ∧
    (∀ (r : ℝ) (v : Vec d) (p : ℝ),
      primState g r v p = toState ((⟨r, v, p⟩ : CFDLean.Primitive d).toConservative g.γ))

/-- P5-20.3 (physical flux): the paper's Euler flux on a vector `y` is M1's integrated flux on the area vector `y`,
for every state (no admissibility needed: both divide by `ρ` the same way). -/
def P5_20_3 : Prop :=
  ∀ (d : ℕ) (g : Gas) (U : CFDLean.Conservative d) (y : Vec d),
    physFlux g (toState U) y = toState (CFDLean.physicalFlux g.γ U y)

/-- P5-20.4 (entropy and entropy variables in M1 variables): with `W = U.toPrimitive γ = (ρ, v, p)`, the paper's
entropy is `-ρ (ln p - γ ln ρ)/(γ - 1)` and its entropy variables are
`((γ - s)/(γ - 1) - ρ|v|²/(2p), ρv/p, -ρ/p)` with `s = ln p - γ ln ρ` and `|v|²` M1's `squareSum`. -/
def P5_20_4 : Prop :=
  ∀ (d : ℕ) (g : Gas) (U : CFDLean.Conservative d),
    let W := U.toPrimitive g.γ
    let s := Real.log W.pressure - g.γ * Real.log W.density
    entropyFun g (toState U) = -W.density * s / (g.γ - 1) ∧
    entropyVars g (toState U) =
      toState ⟨(g.γ - s) / (g.γ - 1) - W.density * CFDLean.squareSum W.velocity / (2 * W.pressure),
        fun α => W.density * W.velocity α / W.pressure, -W.density / W.pressure⟩

end CFDLean.JST1.Spec
