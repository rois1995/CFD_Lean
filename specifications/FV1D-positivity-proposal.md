# FV1D follow-up proposal — Euler positivity under a local CFL condition

**Proposed for independent review.** This is a new result about the step specified in
[FV1D](FV1D.md). Its implementation target is `CFDLean.Euler1D.step` at the
[PR #26 candidate](https://github.com/rois1995/CFD_Lean/blob/c8a964e35a4b34a95fa50d2e43b4b036a0e4af38/CFDLean/Schemes/Euler/FV1D.lean).
The existing [M1 admissibility predicate](../CFDLean/Physics/Euler/State.lean) means positive density and pressure.

## Proposed claim

| ID | Exact-real statement |
|---|---|
| FVP-P | Let `N ≥ 1`, `γ > 1`, `dx > 0`, `dt ≥ 0`, and `U : ZMod N → Conservative 1`. Assume all old cells are M1-admissible. If `dt * (a(i−1) + a(i)) ≤ 2 * dx` at every cell, then every cell of `Euler1D.step γ dx dt U` is M1-admissible. |

Here `a(i)` is the **actual old-state face speed** used by FV1D between cells `i` and `i+1`:
the maximum of their endpoint values of `|m/ρ| + sqrt(γ p/ρ)`. Both adjacent cells use the same oriented
face. There is one common timestep. Equality in the CFL condition, one-cell grids and zero timesteps belong
to the domain. This is a sufficient condition; sharpness is outside the claim.

## Derivation for review

Write `λ = dt/dx` and work in the existing three conserved coordinates. Expand the two Rusanov faces at
cell `i`. With `aL = a(i−1)`, `aR = a(i)`, and `F` the M1 positive-unit-face flux, the updated state is

```text
(1 − λ(aL+aR)/2) Uᵢ
  + (λ aL/2) (Uᵢ₋₁ + F(Uᵢ₋₁)/aL)
  + (λ aR/2) (Uᵢ₊₁ − F(Uᵢ₊₁)/aR).
```

Admissible endpoints have positive sound speed, so both face speeds are strictly positive. The three
coefficients are nonnegative and sum to one. At CFL equality the middle cell can have zero weight.

To check the two split states, put `t = ±1/a`, `v = m/ρ`, `c² = γp/ρ`, and `k = 1+t v`. Since
`a ≥ |v|+c`, one has `k ≥ c/a > 0`. For `U′ = U+t F(U)`, expand the M1 flux to obtain

```text
ρ′ = ρ k
2ρ′ E′ − m′² = k² (2ρ E − m²) − t² p²
             ≥ (p²/a²) (2γ/(γ−1) − 1) > 0.
```

For positive density this determinant inequality is equivalent to positive ideal-gas pressure. Finally,
admissibility is convex in the conserved coordinates: for nonnegative weights summing to one,
weighted Cauchy–Schwarz bounds the kinetic energy of the mixture by the weighted kinetic energies.
The weighted internal energy stays strictly positive even if some weights vanish. These arguments should
be applied to the existing M1 definitions and the actual assembled step. The split states are proof devices.

## Controls and boundary

- Use the [FV1D three-cell data](FV1D.md#exact-control-for-the-euler-step) with `dx = 1` and `dt = 1/3`.
  The right-face speeds are `(3, 2, 3)`. Cell 0 attains CFL equality. Expected densities and momenta
  are `(22/3, 17/6, 23/6)`; energies equal `2 + ρ/2`, giving pressure two in each updated cell.
- Exercise `dt = 0` and the one-cell periodic seam directly. No positive lower bound on `dt` or mesh size
  beyond `N ≥ 1` should enter the public theorem.
- For repeated Forward Euler steps, FVP-P would apply by induction when the condition holds on each
  newly computed field. The first step's speed does not establish later CFL conditions. SSP stages,
  timestep selection, arrays and floating-point error are separate work.

**Review decision requested.** Check the face signs, endpoint-speed bound, non-strict CFL and strict output
pressure against the actual candidate. Recommend freezing FVP-P or give mandatory changes.
