import CFDLean.Exec.NonuniformKernel

/-! FVNA native smoke test: the non-uniform kernels of `CFDLean.Exec.NonuniformKernel` run in `Float` on the
control data. The output is printed, not proved; the exact real values are the FVNA controls.

- Edges: an empty input (empty output), one cell (the seam reads the cell itself, so the step is the identity) and
  `dt = 0` on the FVN-BC data (the identity).
- FVN-BC (Burgers): widths `(1, 3, 1, 1)`, state `(0, 1, 1.2, 0)`, `dt = 0.1`. Exact first order
  `(1/40, 1463/1500, 1141/1000, 27/250)`; exact minmod MUSCL `(289/16000, 23327/24000, 18529/16000, 27/250)`.
- FVN-E (Euler, `γ = 2`): widths `(1, 2, 1)`, densities `(1, 4, 9)` with velocity one and pressure two,
  `dt = 1/16`. Exact densities `(35/16, 249/64, 257/32)`, momenta equal to the densities, energies
  `(99/32, 505/128, 385/64)`. -/
namespace CFDLean.Exec.NonuniformKernelSmoke

open CFDLean.Exec

/-- The FVN-BC widths. -/
def bcWidths : Array Float := #[1, 3, 1, 1]

/-- The FVN-BC state. -/
def bcState : Array Float := #[0, 1, 1.2, 0]

/-- The FVN-E widths. -/
def eWidths : Array Float := #[1, 2, 1]

/-- The Float Euler model at `γ = 2`. -/
def eModel : FV1D.Model Float (FV1D.EulerState Float) := FV1D.euler 1 2 2 Float.abs Float.sqrt max

/-- Density `ρ`, velocity one and pressure two at `γ = 2`. -/
def eState (ρ : Float) : FV1D.EulerState Float := FV1D.triple ρ ρ (2 + ρ / 2)

/-- The three stored components of an Euler state, for printing. -/
def components (s : FV1D.EulerState Float) : Array Float := #[s 0, s 1, s 2]

/-! ### Edges -/

#eval FV1D.nonuniformStepArray FV1D.burgers (0.5 : Float) 0.1 #[] #[]
#eval nuLimiterEulerStepArray Limiter.minmod (0.1 : Float) #[] #[]
#eval nuLimiterSsprk2StepArray Limiter.minmod (0.1 : Float) #[] #[]
#eval nuLimiterSsprk3StepArray Limiter.minmod (0.1 : Float) #[] #[]

#eval FV1D.nonuniformStepArray FV1D.burgers (0.5 : Float) 0.1 #[2] #[0.7]
#eval nuLimiterEulerStepArray Limiter.vanAlbada (0.1 : Float) #[2] #[0.7]
#eval nuLimiterSsprk2StepArray Limiter.none (0.1 : Float) #[2] #[0.7]
#eval nuLimiterSsprk3StepArray Limiter.superbee (0.1 : Float) #[2] #[0.7]

#eval FV1D.nonuniformStepArray FV1D.burgers (0.5 : Float) 0 bcWidths bcState
#eval nuLimiterEulerStepArray Limiter.vanLeer (0 : Float) bcWidths bcState
#eval nuLimiterSsprk2StepArray Limiter.mc (0 : Float) bcWidths bcState
#eval nuLimiterSsprk3StepArray Limiter.minmod (0 : Float) bcWidths bcState

/-! ### FVN-BC, Burgers -/

#eval FV1D.nonuniformStepArray FV1D.burgers (0.5 : Float) 0.1 bcWidths bcState
#eval nuLimiterEulerStepArray Limiter.minmod (0.1 : Float) bcWidths bcState
#eval nuLimiterSsprk2StepArray Limiter.minmod (0.1 : Float) bcWidths bcState
#eval nuLimiterSsprk3StepArray Limiter.minmod (0.1 : Float) bcWidths bcState

/-! ### FVN-E, Euler -/

#eval (FV1D.nonuniformStepArray eModel (0.5 : Float) (1 / 16) eWidths #[eState 1, eState 4, eState 9]).map components

end CFDLean.Exec.NonuniformKernelSmoke
