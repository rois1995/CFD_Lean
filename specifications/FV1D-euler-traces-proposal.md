# Proposed Euler MUSCL face reconstruction on a uniform periodic mesh

**Status: proposal for review.** The [accepted driver](../reviews/FV1D/Driver_Acceptance.md) uses first-order Euler.
This candidate covers what a Rusanov face sees when a uniform Euler reconstruction is introduced. A step CFL,
positivity of updated cell means, non-uniform geometry and enabling a new CLI mode each require further work.

## Reconstruction and ownership

Let `Uᵢ = (ρ,m,E)` be the average in cell `i`. Assume `γ > 1` and every mean has positive density and pressure
`p = (γ−1)(E−m²/(2ρ))`. Limit the backward and forward differences of each **conservative** component with minmod.
The resulting cell slope `sᵢ` gives the two raw traces `Uᵢ − sᵢ/2` and `Uᵢ + sᵢ/2`. Use both if both are
admissible. Otherwise use `(Uᵢ,Uᵢ)`. One choice for the entire cell preserves the arithmetic mean of its traces.
At the face between cells `i` and `i+1`, use the right trace of `i` and the left trace of `i+1`, including
the periodic seam. Compute a numerical flux once for that face. Both adjacent updates must use the same value.

The fallback is deliberately discontinuous at the admissibility boundary. It needs no floor or tuning constant
and may locally reduce the reconstruction to first order. Primitive-variable or characteristic limiting would
give different methods. Choosing conservative variables makes preservation of the stored cell mean explicit.

## Claims to review

- Both selected traces satisfy the M1 density and pressure conditions at the specified `γ`.
- Their mean equals the parent conservative state. Admissible raw traces are retained exactly.
- A constant field gives identical traces on both sides of every face. Include a nonconstant valid stencil to
  exercise the higher-order branch and a counterexample to unguarded componentwise limiting.
- Face admissibility suffices to evaluate the ideal-gas endpoint speed over the reals. It supplies no positivity
  certificate for an updated cell average or for later Runge–Kutta stages.

## Exact counterexample

At `γ = 2`, use the three consecutive means `(1,−3,5), (1,−2,3), (1,−1,3)`. Their pressures are `1/2,1,5/2`.
The middle slope is `(0,1,0)`. Its raw left trace `(1,−5/2,3)` has pressure `−1/8` while the right trace
has pressure `15/8`. The cell must fall back on **both** sides. An independently bounded slope for each
component alone does not keep the conservative state in the pressure-positive set.

Review the variable choice, strict inequalities, fallback granularity and periodic face ownership before a freeze.
[Existing Euler model](../CFDLean/Exec/FV1D.lean) · [Existing scalar limiter](../CFDLean/Exec/LimiterKernel.lean)
