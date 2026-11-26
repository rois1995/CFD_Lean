# P5 proposal: Ismail-Roe smoothness (G6) and the link to the M1 Euler physics

Written 2026-11-26. Same process as P4. Paper input unchanged: `Handbook/paper1/paper1.tex`, sha256 `32e1f260…`.
P1-P4 stay frozen; P5 only adds files. The user authorized the whole cycle (proposal, independent statement review,
self-freeze, proofs, audit, commit, merge) without stopping for approvals.

## 1. Items

| # | Source | What | Size |
|---|---|---|---|
| 19 | `prop:consistency`(b) (line 285, proof 952); gap G6 | the log mean and the Ismail-Roe flux are smooth across the diagonal; P4-16.2 for the Ismail-Roe flux | S-M |
| 20 | TODO item 4 (open part of MR-2) | bridge theorems between `CFDLean/Papers/JST1/Euler/State.lean` and `CFDLean/Physics/Euler` (M1) | S |

## 2. Statement sketches

### Item 19 — G6

- **P5-19.1.** `logMean` is `Cⁿ` for every `n` on `(0, ∞)²`. Proof idea: `logMean a b = a · E(ln b - ln a)` with
  `E = dslope exp 0` (`E(t) = (eᵗ - 1)/t`, `E(0) = 1`), and `E` is analytic (Mathlib: `AnalyticAt.dslope`).
- **P5-19.2.** The admissible set is open, and `(U_a, U_b) ↦ ismailRoe g U_a U_b y` is `Cⁿ` on admissible ×
  admissible for every `n` (all square roots, logarithms and divisions act on positive quantities there).
- **P5-19.3.** Corollary: at every admissible `u0`, `F^IR(u_i, u_k; y) - ½(F(u_i) + F(u_k))·y =
  O(|u_k - u_i|²)` at `(u0, u0)`. Proof: P4-16.2 with P5-19.2 (n = 2) and the symmetry and consistency of P1-2.x.

### Item 20 — paper Euler definitions vs M1

New definitions (bridge only, in the statement file): `toState : Conservative d → State d`,
`ofState : State d → Conservative d`.

- **P5-20.1.** `toState`, `ofState` are inverse; components `ρ, ρv, ρE` agree.
- **P5-20.2.** Pressure, admissibility, velocity and the primitive-to-conservative map agree (`γ = g.γ`).
- **P5-20.3.** The physical flux agrees for every state and vector (`physFlux g (toState U) y =
  toState (physicalFlux g.γ U y)`).
- **P5-20.4.** M1 has no entropy. The paper's entropy and entropy variables, written in M1's primitive variables
  `W = U.toPrimitive γ`.

## 3. Decisions (self-decided under the user's instruction; reason given)

- **D1 — smoothness class (19.1, 19.2).** `∀ n : ℕ, ContDiffOn ℝ n` (C^k for all finite k). Reason: P4-16.2 needs
  C²; "for all n" says "smooth" in the classical sense without the `∞`/`ω` notation of `WithTop ℕ∞`. Analyticity is
  not stated (not needed).
- **D2 — domain (19.2).** Admissible × admissible (`ρ > 0`, `p > 0`), the domain where the flux is used and where
  `√(ρ/p)`, `√(ρp)` are smooth; openness is part of the statement because P4-16.2 needs an open set.
- **D3 — norm (19.3).** The sup norm of `State d = Channel d → ℝ` (Mathlib's Pi norm); all norms are equivalent in
  finite dimension, so the big-O does not depend on the choice.
- **D4 — bridge maps (20).** Two new total maps in the Spec file (not in the frozen `Euler/State.lean`); no frozen
  definition changes.
- **D5 — what is not bridged (20).** Listed in `P5.md`: M1 has no entropy, entropy variables, enthalpy state or
  Ismail-Roe flux; the paper has no M1 coordinate Jacobian (`PhysicalJacobian.lean`, d = 3) and no Roe flux; M1's `γ`
  is a bare real, the paper's `Gas` carries `1 < γ`.

## 4. Later batches (proposals only, not started)

- **P6 (optional) — `∫_T φ_i = m_T`.** Needs the Lebesgue measure of a simplex image and the integral of an affine
  function over it (Mathlib has no simplex measure with barycentric integrals). Sketch: define the simplex as the
  affine image of the standard simplex `{t ≥ 0, Σt ≤ 1}`, use the change of variables (`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`)
  and compute `∫_{Δ_d} t_i = 1/(d+1)!` by induction on `d` (Fubini). Size: M-L. To be proposed separately before
  starting.
- **Mixed meshes with trilinear hexahedra.** Research size (non-affine maps, the Jacobian is not constant, the
  median-dual identities hold only split by split); proposal only.
