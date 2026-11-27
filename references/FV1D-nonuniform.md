# FVN — FV1D on a non-uniform periodic 1D mesh

Status: **implemented, independent implementation review pending.**

The [contract](../specifications/FV1D-nonuniform.md) was frozen at `3eb7cae` after
[independent proposal review](../reviews/FVN/Scientific_Proposal_Review.md).
[Result bindings](../specifications/FV1D-nonuniform-results.json) ·
[Freeze record](../specifications/FV1D-nonuniform-approval.md) ·
[Trusted statement review](../reviews/FVN/TrustedStatements_Review.md)

The milestone changes only the geometry. Every cell has its own width. The mesh stays periodic, cell-centered and
fixed in time. The face flux is any two-point flux `H`, with the FV1D Rusanov face as the model instance, and the time
step is Forward Euler with one `dt`. `Mesh1D` is a fixed periodic 1D mesh. It is not a general control-volume
interface, and the milestone adds no ALE or AMR. FVN adds new modules only. The `Grid`, `FiniteVolume`, `Muscl`,
`Limiters` and `FV1D` definitions are unchanged and are reached only through FVN-U.

## Layering

`update` is reconstruction-independent. It takes a face-flux function `h : I → S` and divides the flux difference of
each cell by the cell's own width. It knows nothing about slopes, limiters, order or stencils, and FVN-C is a property
of `update` alone. First order and MUSCL are two producers of face fluxes for it: the first-order step passes
`H (U i) (U (next i))`, the MUSCL step passes `H (left i) (right i)`. The reconstruction code (`backDiff`, `fwdDiff`,
`slope`, `leftState`, `rightState`, `musclStep`, `componentwise`) is intentionally MUSCL-specific. A general
reconstruction or interface-trace abstraction is deferred until a structurally different reconstruction family is
added. `Mesh1D.lean` and `Nonuniform.lean` import no MUSCL, limiter, Burgers or Euler module.

## Module map

| Module | Purpose |
|---|---|
| [`Mesh1D`](../CFDLean/Discrete/Periodic/Mesh1D.lean) | `Mesh1D` (grid and positive widths), `spacing` (centroid distance `δ`), `uniform`, `MeshRatio` |
| [`Nonuniform`](../CFDLean/Discrete/Periodic/Nonuniform.lean) | Generic `update` and first-order step; FVN-C, first-order FVN-K, FVN-U(a) |
| [`NonuniformMuscl`](../CFDLean/Discrete/Periodic/NonuniformMuscl.lean) | Rescaled MUSCL face states and step over any state type; MUSCL FVN-K and FVN-C, FVN-A |
| [`NonuniformMusclStability`](../CFDLean/Discrete/Periodic/NonuniformMusclStability.lean) | Scalar MUSCL with a `SlopeBounded θ` limiter: FVN-R, incremental form, FVN-M |
| [`Burgers.Nonuniform`](../CFDLean/Schemes/Burgers/Nonuniform.lean) | Burgers face and steps: FVN-U(b), FVN-B, FVN-MB |
| [`Euler.Nonuniform`](../CFDLean/Schemes/Euler/Nonuniform.lean) | Euler instance: first-order step and componentwise MUSCL face states (no Euler theorem) |
| [`NonuniformChecks`](../CFDLean/Discrete/Periodic/NonuniformChecks.lean), [`Burgers.NonuniformChecks`](../CFDLean/Schemes/Burgers/NonuniformChecks.lean) | Every public theorem applied to its hypotheses; one-cell grid `ZMod 1`, `dt = 0`, degenerate bounds `hi ≤ lo` |
| [`Burgers.NonuniformControls`](../CFDLean/Schemes/Burgers/NonuniformControls.lean), [`Euler.NonuniformControls`](../CFDLean/Schemes/Euler/NonuniformControls.lean) | Exact controls FVN-X, FVN-BC and FVN-E |
| [`FV1DNonuniformChallenge`](../CFDLean/Verification/FV1DNonuniformChallenge.lean) | Trusted scalar statements; imports only Mathlib |
| [`FV1DNonuniformVerify`](../CFDLean/Verification/FV1DNonuniformVerify.lean) | Nine bridge theorems |
| [`Challenges/FV1DNonuniform.lean`](../Challenges/FV1DNonuniform.lean) | `lake comparator` challenge ([configuration](../Challenges/FV1DNonuniform.comparator.json)) |

## Frozen result IDs

Names without a namespace are in `CFDLean.FV1D.Nonuniform`. `Burgers.` stands for `CFDLean.Burgers.Nonuniform`.

| ID | Binding | Proof |
|---|---|---|
| FVN-U | `firstOrderStep_uniform` (`Nonuniform`), `Burgers.musclStep_uniform` (`Burgers.Nonuniform`); supporting `Burgers.face_eq` | (a) holds by `rfl`: with width `dx` everywhere the update is `FV1D.step`. (b) On the uniform mesh both rescaling factors are `dx / ((dx + dx)/2) = 1`, so the face states are the B3 face states for every limiter. `face_eq` identifies the Burgers face with the B0 Rusanov flux. |
| FVN-K | `firstOrderStep_constant` (`Nonuniform`), `musclStep_constant` (`NonuniformMuscl`) | For a constant state every face has the value `H C C`, so the flux differences vanish. For MUSCL both differences are 0, and `lim 0 0 = 0` gives a zero slope. |
| FVN-C | `update_weighted_sum`, `firstOrderStep_weighted_sum` (`Nonuniform`), `musclStep_weighted_sum` (`NonuniformMuscl`) | `w i • update(h)(U)(i) = w i • U i − dt • (h i − h (prev i))`, because the cell divides by its own width. The predecessor-face sum is reindexed with the grid equivalence. Both steps are instances. The FVN-E control checks the Euler width-weighted sums. |
| FVN-A | `leftState_affine`, `rightState_prev_affine` (`NonuniformMuscl`) | Local affine reconstruction exactness at one fixed cell `i`. If both differences next to `i` are `δ • β`, both rescaled differences equal `w i • β`, so `lim d d = d` gives the slope `w i • β`. The face offsets are then `± (w i / 2) • β`. No global affine field is assumed (freeze record). |
| FVN-B | `Burgers.firstOrderStep_mem`, `Burgers.firstOrderStep_totalVariation_le` (`Burgers.Nonuniform`) | Harten incremental form with `C i = dt / w i · (a i − mean i)/2` and `D i = dt / w (next i) · (a i + mean i)/2`. Both are nonnegative because `\|mean i\| ≤ a i`. The cell CFL gives the bounds, the face CFL the total variation. The B1 lemmas `incrementalUpdate_bounds` and `incrementalUpdate_totalVariation_le` are reused. |
| FVN-R | `leftState_mem`, `rightState_mem` (`NonuniformMusclStability`), `Burgers.meshRatio_needed` (`Burgers.NonuniformControls`); supporting `meshRatio_p_le_one`, `meshRatio_q_le_one` | The rescaled differences turn the slope rules into `\|s i / 2\| ≤ θ p i \|Δ i\|` and `\|s (next i) / 2\| ≤ θ q i \|Δ i\|`, with `p i = w i / (w i + w (next i))` and `q = 1 − p`. The mesh ratio gives `θ p i ≤ 1` and `θ q i ≤ 1`, so the face states stay between the neighbour values (B3b `half_slope_mem_two`). `meshRatio_needed` is the FVN-X control. |
| FVN-M | `musclStep_mem`, `musclStep_totalVariation_le` (`NonuniformMusclStability`); supporting `musclStep_incremental` | The jumps of the face states across face `i` are `Δ i` times a factor in `[1 − θ q i, 1 + θ p i]` and `[1 − θ p i, 1 + θ q i]`. The step is then in incremental form with `C i ≤ (dt / w i) KR (1 + θ p i)` and `D i ≤ (dt / w (next i)) KL (1 + θ q i)`, and the B1 Harten lemmas apply. On a degenerate interval `hi ≤ lo` the state is constant and the step is the identity. |
| FVN-MB | `Burgers.musclStep_iterate_stable`, `Burgers.musclSsprk2Step_iterate_stable`, `Burgers.musclSsprk3Step_iterate_stable` (`Burgers.Nonuniform`) | FVN-M with the B3 Lipschitz certificate `KL = KR = 2A`. Under the mesh ratio `θ p i ≤ 1` and `θ q i ≤ 1`, so both FVN-M conditions follow from `8 · dt · A ≤ w i`. The B2 SSP lemmas give `n` steps of Forward Euler, SSPRK2 and SSPRK3; `n = 1` is the contract's one step. |

Definitions are bound under the ID that introduces them: `Mesh1D`, `uniform`, `update`, `firstOrderStep`,
`Burgers.face` and `Burgers.musclStep` under FVN-U; the generic `musclStep` under FVN-K; the Euler `nonuniformStep`
under FVN-C; `spacing`, the MUSCL face states, `componentwise` and the Euler `musclLeft` and `musclRight` under
FVN-A; `Burgers.firstOrderStep` under FVN-B; `MeshRatio` and the control data `fvnMesh` and `fvnState` under FVN-R;
`Burgers.musclSsprk2Step` and `Burgers.musclSsprk3Step` under FVN-MB.

## Mesh ratio and limiters

The mesh ratio `θ` asks `θ · max(w i, w (next i)) ≤ w i + w (next i)` at every face. Minmod (`θ = 1`) needs no mesh
condition. Van Albada (`θ = 5/4`) needs neighbour widths within a factor of 4. MC, superbee and van Leer (`θ = 2`)
need equal neighbour widths.

Two statements must be kept apart:

1. The `SlopeBounded θ` certificate of B3b does not carry over to stretched cells for `θ = 2`. Control FVN-X shows
   this: on widths `(1, 3, 1, 1)` the van Leer, MC and superbee left states at face 1 leave `[0, 6/5]`.
2. This does not mean that these limiters cannot be used on stretched cells. Limiters whose bound depends on the
   local width ratio are possible and are outside this milestone.

For the wider limiter problem on irregular grids see M. J. Berger, M. J. Aftosmis and S. M. Murman, "Analysis of
slope limiters on irregular grids", AIAA Paper 2005-0490.

## Trusted boundary

The scalar claims FVN-B, FVN-R, FVN-M and FVN-MB and the FVN-X control are restated in a Mathlib-only trusted file.
The file restates the mesh, the rescaled reconstruction and both scalar steps without importing the implementation.
The generic claims FVN-U, FVN-K, FVN-C and FVN-A and the Euler control are checked by the verifier and the kernel
audit only, as for FV1D.

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
|---|---|---|---|
| FVN-B | `FirstOrderBounds`, `FirstOrderTotalVariation` | `first_order_bounds`, `first_order_total_variation` | `Burgers.firstOrderStep_mem`, `Burgers.firstOrderStep_totalVariation_le` |
| FVN-R | `ReconstructionBounds` | `reconstruction_bounds` | `leftState_mem` (and `rightState_mem`) |
| FVN-R | `MeshRatioOvershoot` (FVN-X) | `mesh_ratio_overshoot` | `Burgers.meshRatio_needed` |
| FVN-M | `MusclBounds`, `MusclTotalVariation` | `muscl_bounds`, `muscl_total_variation` | `musclStep_mem`, `musclStep_totalVariation_le` |
| FVN-MB | `MusclEulerMultiStep`, `MusclSSPRK2MultiStep`, `MusclSSPRK3MultiStep` | `muscl_*_multi_step` | `Burgers.musclStep_iterate_stable`, `Burgers.musclSsprk2Step_iterate_stable`, `Burgers.musclSsprk3Step_iterate_stable` |

The [statement review](../reviews/FVN/TrustedStatements_Review.md) by a separate AI agent found no mandatory issue.
No human has reviewed the trusted statements yet.

## Exact controls

All values are exact rationals from the contract, computed independently of Lean.

- **FVN-X** (`meshRatio_needed`). Widths `(1, 3, 1, 1)`, state `(0, 1, 6/5, 0)`. The mesh ratio holds for `θ = 5/4`
  and fails for `θ = 2`. At cell 1 `back = 3/2` and `fwd = 3/10`. The left state at face 1 is `23/20` (minmod) and
  `61/52` (van Albada), inside `[0, 6/5]`, and `5/4` (van Leer), `13/10` (MC, superbee) and `29/20` (unlimited),
  outside.
- **FVN-BC** (`firstOrderStep_fvnMesh`, `musclStep_fvnMesh_minmod` and their sums). Same data, `dt = 1/10`. First
  order gives `(1/40, 1463/1500, 1141/1000, 27/250)` and minmod MUSCL `(289/16000, 23327/24000, 18529/16000,
  27/250)`. Both keep `∑ w i · u i = 21/5`. Two wrong-width mutations fail: the unrescaled B3 slope at cell 1 is
  `1/5` instead of `3/10`, and the update fed with the unrescaled B3 face fluxes gives `81/4000` instead of
  `289/16000` in cell 0. The value `27/250` of cell 3 includes the seam face from cell 3 to cell 0.
- **FVN-E** (`Euler.NonuniformControls`). Widths `(1, 2, 1)`, `γ = 2`, `dt = 1/16`, densities `(1, 4, 9)`, velocity
  one and pressure two. The first-order step gives densities `(35/16, 249/64, 257/32)` with equal momenta and
  energies `(99/32, 505/128, 385/64)`. Cells 0 and 2 match the uniform FV1D control. The width-weighted totals
  `(18, 18, 17)` are kept. The componentwise minmod slopes are `0`, `(4, 4, 2)`, `0`, and all six MUSCL face states
  have velocity one and pressure two. Without rescaling the cell 1 slope would be `(3, 3, 3/2)`.

## Checks

`scripts/verify.py` (result map, axioms, trusted file and challenge hashes, bridge types), `KernelAudit.lean`,
`StatementChecks.lean`, the `--wfail` builds of the checks, controls and bridge modules in CI, and
`lake comparator --paranoid --config Challenges/FV1DNonuniform.comparator.json`.

## Exclusions

No Euler theorem on this mesh (positivity, admissible MUSCL face states). No executable or machine arithmetic, no
entropy result, no non-periodic boundary, no moving mesh, no sharp CFL constant, no mesh-adapted limiter and no general
control-volume interface ([FUTURE §2](../roadmap/FUTURE.md)).
