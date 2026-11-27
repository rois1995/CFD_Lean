# FVN follow-up proposal — executable kernels on the non-uniform mesh and their exact-real refinement

**Status.** Revised after the first independent scientific review ([record](../reviews/FVNA/Proposal_Review_1.md)). Base: `develop` at `660fd4c`, the
[frozen FVN contract](FV1D-nonuniform.md) and its implementation candidate in
[PR #43](https://github.com/rois1995/CFD_Lean/pull/43). Implementation starts after FVN is merged into `develop`.
[Milestone workflow](../CONTRIBUTING.md#milestone-workflow) · [Standing authorization](../reviews/Standing_Authorization.md)

## Purpose

FVN proved the non-uniform first-order and MUSCL steps over the reals. The executable kernels (E0, E0b, E0c, FVA)
still assume one cell width. This milestone, FVNA, adds executable array kernels that take one width per cell and
proves that, interpreted over the reals, they compute exactly the FVN steps. The FVN guarantees then transfer to the
arrays, as E0b and E0c transferred B3 and B3b.

Burgers stays the place where the hard results are proved. The first-order kernel is shared by both models; the Euler
instance gets one exact control and no Euler theorem, as in FVN. Machine arithmetic stays outside the proof boundary:
error bounds for `Float` belong to E1.

## Kernels

All kernels use the existing executable arithmetic (`Scalar α`, and `ScalarSign α` where a limiter tests a sign) and
the periodic indices of [Kernel.lean](../CFDLean/Exec/Kernel.lean). A mesh is a `widths : Array α` with one entry per
cell. The theorems assume `widths.size = u.size`, `n = u.size ≥ 1` and every width positive. The kernels read the
widths with a total accessor, so a size mismatch cannot index out of bounds; checking sizes and signs is the driver's
job.

**First order, shared by both models.** It reuses the FVA `Model` and its `face`:

```text
h i      = face M half u[i] u[i+1]
out[i]   = u[i] − (dt / w[i]) • (h i − h (i−1))
```

**MUSCL with a limiter, scalar.** It reuses the E0c `limiterSlope` and the B0 `rusanov` flux. The differences are
rescaled as in FVN:

```text
back i   = (two * w[i] / (w[i−1] + w[i])) * (u[i] − u[i−1])
fwd i    = (two * w[i] / (w[i] + w[i+1])) * (u[i+1] − u[i])
s i      = limiterSlope L (back i) (fwd i)
left i   = u[i] + s i / two           right i = u[i+1] − s (i+1) / two
out[i]   = u[i] − (dt / w[i]) * (rusanov (left i) (right i) − rusanov (left (i−1)) (right (i−1)))
```

`two * w[i] / (w[i−1] + w[i])` is `w i / δ (i−1)` written without a halving, so the kernel needs no new `Scalar`
capability. SSPRK2 and SSPRK3 are the existing Shu–Osher combinations (`axpby`) over this Euler step.

The existing kernels and the `burgers1d` driver do not change.

## Proposed result map

Let `n ≥ 1`, `dt ≥ 0`, `widths` and `u` real arrays of size `n` with positive widths. Array entry `i` represents
periodic cell `(i.val : ZMod n)`. `mesh widths` is the FVN `Mesh1D` on `zmodGrid n` with those widths.

| ID | Statement |
|---|---|
| FVNA-F | The first-order array kernel over the reals represents the FVN first-order step for the two concrete real models. Burgers: it represents `Burgers.Nonuniform.firstOrderStep (mesh widths) dt u` in every cell. Euler: for every `γ > 1` and every array representing an initially admissible field, it represents `Euler1D.nonuniformStep γ (mesh widths) dt U` in every cell, in all three components. |
| FVNA-M | For every limiter `L` (including `none`), the MUSCL Forward Euler, SSPRK2 and SSPRK3 array kernels over the reals represent `Burgers.Nonuniform.musclStep (mesh widths) dt L.slopeFn` and its SSPRK2 and SSPRK3 combinations in every cell. |
| FVNA-U | If every width equals `dx > 0`, the first-order kernel equals the FVA `stepArray` and the MUSCL kernels equal the E0c `limiterEulerStepArray`, `limiterSsprk2StepArray` and `limiterSsprk3StepArray` with `dx`, entry by entry, over the reals. |
| FVNA-T | Transferred guarantees over the reals. (a) Conservation: for Burgers, every kernel (first order, and MUSCL with every `L` for Forward Euler, SSPRK2 and SSPRK3) keeps `∑ i, w[i] * u[i]`; for Euler, the first-order kernel keeps `∑ i, w[i] * q(U[i])` separately for density, x-momentum and total energy. (b) First order, Burgers: if every entry of `u` lies in `[m, M]` and the FVN-B local conditions hold, the output stays in `[m, M]`; under the FVN-B face condition the total variation does not increase. (c) For `L ≠ none` with mesh ratio `L.theta`, `0 ≤ dt`, every entry of `u` in `[m, M]`, and `8 · dt · max(|m|, |M|) ≤ w[i]` for every `i`: `n` steps of the Forward Euler, SSPRK2 and SSPRK3 kernels keep every entry in `[m, M]` and do not increase the total variation. |

Generic statements over an arbitrary state type are not result IDs. The FVA `Model` record carries arbitrary
operations with no laws, so the shared stencil lemma is stated only for the compatible model
`⟨(· + ·), (· - ·), (· • ·), F, a⟩` over a real module, as in the FVA refinement, and stays a supporting lemma. The
Burgers and Euler real models are then shown equal to such compatible models. Make the face and width alignment one
explicit refinement lemma: the right state at face `i` uses the slope of `i + 1`, whose backward rescaling uses the
same pair `w[i]`, `w[i+1]` (including the seam). In FVNA-T (a), one-step conservation follows from flux
cancellation; SSPRK2 and SSPRK3 keep the same linear invariant because their real coefficients sum to one. The bounds
hypotheses in (b) and (c) are written with the existing `EntriesBetween m M u`.

FVNA-T (c) inherits the FVN finding: minmod works on any mesh, van Albada needs neighbour widths within a factor of 4,
and MC, superbee and van Leer need equal neighbour widths.

## Controls

- **Burgers.** The FVN-BC data (widths `(1, 3, 1, 1)`, state `(0, 1, 6/5, 0)`, `dt = 1/10`) through the real array
  kernels: first order `(1/40, 1463/1500, 1141/1000, 27/250)` and minmod MUSCL
  `(289/16000, 23327/24000, 18529/16000, 27/250)`.
- **Euler.** The FVN-E data (widths `(1, 2, 1)`, `γ = 2`, `dt = 1/16`) through the real first-order array kernel:
  densities `(35/16, 249/64, 257/32)`, momenta equal to the densities, energies `(99/32, 505/128, 385/64)`.
- **Edges.** One cell, `dt = 0`, and an empty input (empty output, no indexing; outside the physical theorems).
- **Native smoke test.** Both kernels run in `Float` on the control data; the output is printed, not proved.

## Review boundary and evidence

Bind each result ID to qualified theorem names, check statements and axioms through the verifier and kernel audit,
and add the controls as Lean checks. Like E0b and E0c, FVNA-M and FVNA-T get a trusted challenge whose statement
file imports Mathlib plus the hash-pinned kernel modules (`trusted_inputs`). Preserve every existing binding and pin;
the existing kernels, refinement theorems and driver do not change.

Outside this milestone: any driver change. A non-uniform mesh option belongs to the planned general driver
`fv1d --model burgers|euler`, not to `burgers1d`. Also outside: `Float` error bounds (E1), Euler MUSCL, Euler
positivity on the non-uniform mesh, and mesh-adapted limiters.

**Review decision requested.** Check the rescaled array differences against FVN, the index and width alignment
(including the seam), the transferred hypotheses, and the controls. Recommend freezing FVNA-F, FVNA-M, FVNA-U and
FVNA-T, or give mandatory changes.
