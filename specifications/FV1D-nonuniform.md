# FV1D follow-up proposal — non-uniform periodic 1D mesh, first order and MUSCL

**Status.** Proposed for independent scientific review. Base: `develop` at `8f5dff5`, the
[frozen FV1D step](FV1D.md) and its [PR #26 implementation candidate](https://github.com/rois1995/CFD_Lean/tree/c8a964e35a4b34a95fa50d2e43b4b036a0e4af38).
Freeze the reviewed claims before theorem-bearing implementation. Implementation starts after FV1D is merged into
`develop`, because it reuses `CFDLean.FV1D.face` and `CFDLean.FV1D.step`.
[Milestone workflow](../CONTRIBUTING.md#milestone-workflow) · [Standing authorization](../reviews/Standing_Authorization.md)

## Purpose and working rule

This milestone changes the geometry and keeps everything else fixed. FV1D has one cell width `dx`. Here every cell
has its own width. The mesh stays periodic, cell-centered and fixed in time. The face flux stays Rusanov. Time
stepping stays Forward Euler with one common `dt`. This is the stress test named in
[PRINCIPLES §16](../roadmap/PRINCIPLES.md) and [NEXT, Priority 1](../roadmap/NEXT.md).

The milestone uses Burgers to build and prove the shared foundations. The claims have three layers:

| Layer | What it contains | Models |
|---|---|---|
| Generic | Definitions and results for any conserved-state type `S` with real vector arithmetic | All |
| Scalar | Bounds and total variation. These need an order on states. | Burgers (and any scalar flux with the B3 certificate) |
| Euler check | An Euler instance of each generic definition and one exact control. No Euler theorem. | Euler |

The Euler check shows that the generic definitions fit a system. Euler theorems on this mesh, for example
positivity, belong to later proposals.

## Geometry

Take a finite index type `I` with a periodic `Periodic.Grid I` (successor `next`, predecessor `prev`). The face
indexed by `i` points from cell `i` to `next i`. A mesh is the grid plus one width per cell:

```text
structure Mesh1D (I) where
  grid      : Periodic.Grid I
  width     : I → ℝ
  width_pos : ∀ i, 0 < width i
```

The positivity field is the geometric validity hypothesis ([PRINCIPLES §5](../roadmap/PRINCIPLES.md)). In 1D the
centroid of a cell is its midpoint. So the width is the only geometric input. Derived quantities:

```text
w i        = width i
δ i        = (w i + w (next i)) / 2            distance between the centroids of i and next i
uniform g dx  : the mesh with width fun _ => dx, for dx > 0
```

The field stays separate from the mesh. A state is `U : I → S` over a given mesh
([PRINCIPLES §4](../roadmap/PRINCIPLES.md)). The supported grids include `zmodGrid N` for every `N ≥ 1`.
`N = 1` and `dt = 0` belong to the domain.

## The step

For any face-flux function `h : I → S`, the flux-form update is

```text
update(h)(U)(i) = U i − (dt / w i) • (h i − h (prev i))
```

The cell divides by its own width. Two face fluxes enter this update. Both evaluate the old state.

Both steps take a general two-point face function `H : S → S → S`. The model's Rusanov face
`H = FV1D.face F a`, with physical flux `F` and speed `a` from the frozen FV1D contract, is the instance for both
models. For scalar claims, `H = nf.eval` for a B3 `NumericalFlux nf`. The existing bridge between the Burgers
FV1D face and the B0 Rusanov flux connects the two for Burgers.

**First order.** `h i = H (U i) (U (next i))`.

**MUSCL.** The model supplies a limiter `lim : S → S → S`. Differences are first rescaled to one cell width:

```text
back i  = (w i / δ (prev i)) • (U i − U (prev i))
fwd i   = (w i / δ i)        • (U (next i) − U i)
s i     = lim (back i) (fwd i)
left i  = U i        + (1/2) • s i                 left state at face i
right i = U (next i) − (1/2) • s (next i)          right state at face i
h i     = H (left i) (right i)
```

On a uniform mesh `w i / δ j = 1`, so this is the B3 reconstruction with no change. This holds for every limiter.
A positively homogeneous limiter gives the same face states as the gradient form `σ = lim(D⁻, D⁺)` with
`D = ΔU / δ` and face offset `(w i / 2) • σ`. The rescaled form needs no homogeneity.

Instances:

- **Scalar (Burgers).** `S = ℝ`, `F u = u²/2`, `a` is the B0 Rusanov speed `max(|L|, |R|)`, `lim = φ` for any
  B3/B3b slope function, including `centralSlope` (unlimited) and the five limited slopes.
- **Euler.** `S = Vector 3` through the FV1D encoding of M1 `Conservative 1`. `F` and `a` are the FV1D Euler flux and
  endpoint speed. The limiter acts on each conserved component: `lim A B k = φ (A k) (B k)`, for density,
  x-momentum and total energy. Characteristic or primitive-variable limiting is outside this milestone.

## Proposed result map

### Generic claims (any `S`, `H`, `lim`)

| ID | Statement |
|---|---|
| FVN-U | On `uniform g dx` with `dx > 0`: (a) with `H = FV1D.face F a`, the first-order step equals `FV1D.step g F a dx dt U` in every cell; (b) for `S = ℝ` with the Burgers face and any `φ`, the MUSCL step equals `Burgers.musclEulerStep g dx dt φ u` in every cell. |
| FVN-K | For a constant state `fun _ => C`, both steps return `C` in every cell, for every `H`. Every face then has the same value `H C C`, so the flux differences vanish. The MUSCL part assumes `lim 0 0 = 0`. |
| FVN-C | For every face-flux function `h`, `∑ i, w i • update(h)(U)(i) = ∑ i, w i • U i`. Both steps are instances. Only the generic theorem is bound. For Euler the FVN-E control checks the width-weighted sums of density, momentum and energy. |
| FVN-A | Affine data are rebuilt exactly. Let `lim d d = d` for all `d`. If `U (next i) − U i = δ i • β` and `U i − U (prev i) = δ (prev i) • β` for some `β : S`, then `left i = U i + (w i / 2) • β` and `right (prev i) = U i − (w i / 2) • β`. |

FVN-A is the main check that the geometry enters correctly. The uniform-grid formula fails it on a non-uniform
mesh. All six B3b slopes satisfy `lim d d = d`.

### Scalar claims

Write `a i` for the Burgers face speed `max(|u i|, |u (next i)|)`. Let `m ≤ u j ≤ M` for all `j`.
"Mesh ratio `θ`" means `θ · max(w i, w (next i)) ≤ w i + w (next i)` at every face `i`.

| ID | Statement |
|---|---|
| FVN-B | First-order Burgers, `dt ≥ 0`. (a) Bounds: if `dt · (a (prev i) + a i) ≤ w i` at every cell, every output is in `[m, M]`. (b) Total variation: if `dt · a i ≤ min(w i, w (next i))` at every face, `TV(step u) ≤ TV(u)`, where `TV(u) = ∑ i, \|u (next i) − u i\|`. |
| FVN-R | Reconstruction bounds. If `φ` is `SlopeBounded θ` and the mesh ratio `θ` holds, then `left i` and `right i` are in `[m, M]` for every face. |
| FVN-M | Scalar MUSCL with `H = nf.eval` for a `NumericalFlux nf` that is `MonotoneFlux` and has the B3 Lipschitz certificate `LipschitzOnBounds nf m M KL KR`, `φ` `SlopeBounded θ`, mesh ratio `θ`, `dt ≥ 0`. (a) Bounds, if at every cell `dt · [(KL + KR)/w i + θ · (KR/(w i + w (next i)) + KL/(w (prev i) + w i))] ≤ 1`. (b) Total variation, if at every face `dt · [KR/w i + KL/w (next i) + θ · (KL + KR)/(w i + w (next i))] ≤ 1`. |
| FVN-MB | Burgers MUSCL. Let `A = max(\|m\|, \|M\|)`, `φ` `SlopeBounded θ`, mesh ratio `θ`, and `8 · dt · A ≤ w i` for every cell. Then Forward Euler, iterated any number of times, and one SSPRK2 or SSPRK3 step keep `[m, M]` and do not increase `TV`. |

**Reduction to the accepted results.** On a uniform mesh the mesh ratio `θ` is `θ ≤ 2` (B3b). The FVN-M conditions
become `dt (1 + θ/2)(KL + KR) ≤ dx`, the B3b condition. The FVN-B conditions become `dt (a(i−1) + a i) ≤ dx` and
`dt · a i ≤ dx`. B1 uses the stronger `2 · dt · A ≤ dx`. FVN-MB uses one constant for all `θ ≤ 2`, so it is weaker
than B3b on a uniform mesh. All constants are sufficient, not sharp.

**What the mesh ratio means.** Minmod (`θ = 1`) needs no mesh condition. Van Albada (`θ = 5/4`) needs neighbor
widths within a factor of 4. MC, superbee and van Leer (`θ = 2`) need equal neighbor widths. So the B3b certificate
for `θ = 2` does not carry over to a non-uniform mesh in this form. Control FVN-X shows that the reconstruction
bound really fails. Limiters whose bound depends on the local width ratio are a possible follow-up. The reviewer is
asked to name the reference result for this, if one exists (a candidate is Berger, Aftosmis and Murman, "Analysis
of slope limiters on irregular grids", AIAA 2005-0490).

**Derivation sketch for FVN-M.** Put `p i = w i/(w i + w (next i))` and `q i = w (next i)/(w i + w (next i))`.
The slope rules give `|s i / 2| ≤ θ · p i · |Δ i|` against the forward difference and
`|s i / 2| ≤ θ · q (prev i) · |Δ (prev i)|` against the backward difference, with matching signs. So
`(left i − left (prev i))/Δ (prev i)` is in `[1 − θ p (prev i), 1 + θ q (prev i)]` and
`(right i − right (prev i))/Δ i` is in `[1 − θ q i, 1 + θ p i]`. The mesh ratio keeps both nonnegative. The
step is a Harten incremental update with `C i ≤ (dt/w i) KR (1 + θ p i)` and
`D (prev i) ≤ (dt/w i) KL (1 + θ q (prev i))`. The existing lemmas `incrementalUpdate_bounds` and
`incrementalUpdate_totalVariation_le` then apply without change. Under the mesh ratio `θ p i ≤ 1` and
`θ q i ≤ 1`, which gives FVN-MB from FVN-M with `KL = KR = 2A`.

## Exact controls

All values are exact rationals. They were computed independently of Lean.

**FVN-X (mesh ratio needed).** Four cells, widths `(1, 3, 1, 1)`, state `u = (0, 1, 6/5, 0)`, so `M = 6/5`.
At cell 1, `back = 3/2` and `fwd = 3/10`. The left state at face 1 is:

| Slope | `left 1` | In `[0, 6/5]`? |
|---|---|---|
| minmod | `23/20` | yes |
| van Albada | `61/52` | yes |
| van Leer | `5/4` | no |
| MC, superbee | `13/10` | no |
| unlimited | `29/20` | no |

The mesh ratio holds for `θ = 5/4` (`15/4 ≤ 4`) and fails for `θ = 2` (`6 > 4`).

**FVN-BC (Burgers step).** Same mesh and state, `dt = 1/10`. Then `8 · dt · A = 24/25 ≤ 1 = min w`.

| Step | Cells 0–3 |
|---|---|
| First order | `(1/40, 1463/1500, 1141/1000, 27/250)` |
| MUSCL, minmod | `(289/16000, 23327/24000, 18529/16000, 27/250)` |

Both keep `∑ w i · u i = 21/5` and stay in `[0, 6/5]`. The B3 reconstruction without rescaling gives
`81/4000` in cell 0 instead of `289/16000`. Division by the wrong cell width or a reversed update sign also fails
this control.

**FVN-E (Euler check).** The FV1D control data on a non-uniform mesh: three cells, widths `(1, 2, 1)`, `γ = 2`,
`dt = 1/16`, densities `(1, 4, 9)`, velocity one and pressure two in each cell, so states `(ρ, ρ, 2 + ρ/2)`.

- First-order step: densities `(35/16, 249/64, 257/32)`, momenta equal to the densities, energies
  `(99/32, 505/128, 385/64)`. Cells 0 and 2 match the uniform FV1D control. Cell 1 has width 2 and gets half of
  its uniform update. The width-weighted totals `(18, 18, 17)` are kept. Pressure stays two in every cell.
- MUSCL face states with componentwise minmod: slopes `0`, `(4, 4, 2)`, `0`. Left states
  `((1,1,5/2), (6,6,5), (9,9,13/2))`, right states `((2,2,3), (9,9,13/2), (1,1,5/2))`. Every face state has velocity
  one and pressure two. Without rescaling, the cell 1 slope would be `(3, 3, 3/2)`.

The full Euler MUSCL step is not a control, because the face sound speeds are irrational.

## Review boundary and evidence

At implementation, bind each result ID to qualified theorem names, check the exact statements and axioms through the
verifier and kernel audit, and add the three controls as Lean checks.

**Trusted challenge for the scalar claims.** Like B1–B3b, the scalar claims get a Mathlib-only trusted statement
module, bridge theorems and a `lake comparator` challenge (`Challenges/FV1DNonuniform.lean` with its
`.comparator.json`, permitted axioms `propext`, `Quot.sound`, `Classical.choice`). The challenge covers FVN-B,
FVN-R, FVN-M, FVN-MB and the FVN-X counterexample. It restates the mesh, the rescaled reconstruction and both
scalar steps without importing the implementation. The [B3b challenge](../Challenges/BurgersB3b.lean) is the
model to adapt. The generic claims FVN-U, FVN-K, FVN-C, FVN-A and the Euler control are checked through the
verifier and kernel audit only, as for FV1D. Each trusted statement gets an AI statement review before merge.
Human review of the trusted statements follows the open Priority 0 item. Preserve all B0–B4, B3b, FV1D and M1 bindings
and pins. The existing `Grid`, `FiniteVolume`, `Muscl`, `Limiters` and `FV1D` definitions do not change. The new
definitions live in their own modules and reach the old ones only through FVN-U.

Outside this milestone: Euler theorems on this mesh (positivity, admissible MUSCL face states), executable and
machine arithmetic, entropy, non-periodic boundaries, moving meshes, sharp CFL constants, mesh-adapted limiters and a
general control-volume interface ([FUTURE §2](../roadmap/FUTURE.md)).

**Review decision requested.** Check the rescaled reconstruction, the mesh-ratio condition, the local CFL conditions
and the three controls. Recommend freezing FVN-U, FVN-K, FVN-C, FVN-A, FVN-B, FVN-R, FVN-M and FVN-MB, or give
mandatory changes.
