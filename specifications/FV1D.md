# FV1D proposal — one periodic Rusanov step for Burgers and Euler

**Status.** Proposed for independent scientific review on the `4c77f6e` baseline. This document defines the
first exact-real milestone on the shared 1D path. Freeze the reviewed claims before theorem-bearing implementation.
[Milestone workflow](../CONTRIBUTING.md#milestone-workflow) · [Standing authorization](../reviews/Standing_Authorization.md)

## The common step

Take `N : ℕ` with `[NeZero N]`, cell indices `ZMod N`, a common cell width `dx > 0` and a common time step
`dt ≥ 0`. Include `N = 1` and `dt = 0`. Cell averages are measured per unit cross-sectional area. Use the existing
`zmodGrid N`, whose successor adds one. The face indexed by `i` points from cell `i` to its successor.
[Periodic grid](../CFDLean/Discrete/Periodic/Grid.lean)

For a conserved state space with real vector arithmetic, let `F` be the physical flux in the positive x direction
and `a(L,R)` the chosen scalar dissipation speed. For cell data `U`, evaluate both faces at the old time level:

```text
H(L,R)     = (1/2) • (F(L) + F(R)) − (a(L,R)/2) • (R − L)
h(i)       = H(U(i), U(i+1))
step(U)(i) = U(i) − (dt/dx) • (h(i) − h(i−1))
```

Here `•` scales all conserved components. Both models must instantiate this same face formula and step. Expose
only the state arithmetic and model operations these formulas consume. Physical admissibility is a predicate on
input states. Fluxes and state differences live in the ambient vector space. Both equations have zero source.

## Model data

| | Burgers | Ideal-gas Euler |
|---|---|---|
| Conserved state | A real cell average `u` | `Conservative 1` with components `(ρ, m, E)`, where `m = momentum 0` and `E` is total energy density |
| Physical domain | All real states | Fixed `γ > 1`, `ρ > 0` and `p = (γ−1)(E − m²/(2ρ)) > 0`, using M1 admissibility |
| Positive-x physical flux | `u²/2` | M1 `physicalFlux γ U (fun _ => 1)`, with components `(m, m v + p, (E+p)v)` and `v = m/ρ` |
| Dissipation speed | Maximum absolute value of the two endpoint states | Maximum of the two endpoint values of `abs(v) + sqrt(γ p/ρ)` |

Use the existing Burgers physical flux and M1 state, pressure and flux definitions. An Euler coordinate adapter
must recover all three M1 components exactly. The endpoint-speed formula fixes the numerical method. Conservation
follows from using the same face flux in adjacent cells and is independent of a spectral estimate or CFL bound.
[Burgers Rusanov](../CFDLean/Schemes/Burgers/Rusanov.lean) · [M1 state](../CFDLean/Physics/Euler/State.lean) ·
[M1 physical flux](../CFDLean/Physics/Euler/PhysicalFlux.lean)

## Proposed result map

| ID | Statement to check on the actual instantiated definitions |
|---|---|
| FV1D-B | For every supported `N, dx, dt`, every `u : ZMod N → ℝ` and cell `i`, the Burgers instance at `i` equals `CFDLean.Burgers.Schemes.RusanovForwardEuler.step dx dt u i`. |
| FV1D-F | For every admissible `C : Conservative 1`, the Euler numerical flux `H(C,C)` equals the M1 positive-x physical flux in all three components. |
| FV1D-K | For every admissible constant `C`, the Euler step on `fun _ => C` returns `C` in every cell. |
| FV1D-C | For every initially admissible periodic Euler field, `dx * ∑ i, q(step(U)(i)) = dx * ∑ i, q(U(i))` separately for density, momentum and energy. |

The Euler rows quantify over every fixed `γ > 1`; the step rows use the mesh and time domain above. FV1D-C
requires no hypothesis on the output. Derive the component balances by periodic reindexing. Prove FV1D-B against
the existing assembled operator, so agreement covers neighbor order, old-state evaluation and timestep scaling.
[B0 assembled step](../CFDLean/Schemes/Burgers/RusanovForwardEuler.lean) · [B0 proof map](../references/Burgers-B0.md)

## Exact control for the Euler step

Use three cells in index order `0, 1, 2`, with `γ = 2`, `dx = 1`, `dt = 1/16`, and initial densities
`(1, 4, 9)`. Set velocity to one and pressure to two in each cell, giving states `(ρ, ρ, 2 + ρ/2)`.
The three sound speeds are `(2, 1, 2/3)`. The right-face mass fluxes are `(−2, 3/2, 17)`, including the face
from cell 2 to cell 0. The expected updated densities are `(35/16, 121/32, 257/32)`.
Check these values on the assembled Euler step. Reversing the update sign still preserves the sum, but fails
this control. The momentum and energy updates can also be checked directly using the same density profile.

## Review boundary and evidence

At implementation, bind the four result IDs, check their exact statements and foundational axioms through the
repository verifier and kernel audit, and include the three-cell Lean control. Preserve the existing B0 and M1
bindings and pins. A reviewer should independently recompute the control and check the new Euler flux against M1
and the Burgers specialization against the cited B0 step. Record the verdict against the exact candidate revision.

This milestone ends at one exact-real first-order update. Output positivity for general data needs its own
timestep argument. Entropy, high-order reconstruction, SSP composition, `fv1d`, backend refinement, source terms
and multidimensional geometry belong to later milestones. The existing Roe and median-dual contracts retain their
own scope and review history.
