# FVNA — executable kernels on the non-uniform periodic 1D mesh

Status: **implemented, independent implementation review pending.**

The [contract](../specifications/FV1D-nonuniform-array.md) was frozen at `077a916` after
[independent proposal review](../reviews/FVNA/Scientific_Proposal_Review.md) (first round:
[record](../reviews/FVNA/Proposal_Review_1.md)).
[Result bindings](../specifications/FV1D-nonuniform-array-results.json) ·
[Freeze record](../specifications/FV1D-nonuniform-array-approval.md) ·
[Trusted statement review](../reviews/FVNA/TrustedStatements_Review.md) ·
[FVN proof map](FV1D-nonuniform.md)

FVNA adds executable array kernels that take one width per cell, proves that over the reals they compute exactly the
[FVN](FV1D-nonuniform.md) steps, and transfers the FVN guarantees to the arrays, as E0b and E0c did for B3 and B3b.
The kernels use only the existing `Scalar α` operations, with `ScalarSign α` for the limiter sign test. The existing
kernels, refinement theorems and the `burgers1d` driver are unchanged; FVNA adds new modules only.

## Kernels

A mesh is `widths : Array α`, one entry per cell. The kernels read a width with the total accessor
`widthAt widths i = widths.getD i 0`, so a short `widths` array cannot index out of bounds; checking sizes and signs
is the driver's job. The refinement and transfer theorems assume `widths.size = u.size = n ≥ 1` and positive widths,
so the default is never read there.

- **First order** (`FV1D.nonuniformStepArray`), shared by Burgers and Euler. It reuses the FVA `Model` and `face`:
  `out[i] = u[i] − (dt / w[i]) • (h i − h (i−1))` with `h i = face M half u[i] u[i+1]`.
- **MUSCL with a limiter**, scalar (`nuLimiterEulerStepArray`). It reuses the E0c `limiterSlope` and the B0
  `rusanov` flux. The differences are rescaled as in FVN: `nuBackDiff` is `(two * w[i] / (w[i−1] + w[i])) * (u[i] −
  u[i−1])`, `nuFwdDiff` is `(two * w[i] / (w[i] + w[i+1])) * (u[i+1] − u[i])`, `nuSlopeAt` limits them, `nuLeftState`
  and `nuRightState` are the face states and `nuFaceFlux` the Rusanov flux at face `i`. SSPRK2 and SSPRK3
  (`nuLimiterSsprk2StepArray`, `nuLimiterSsprk3StepArray`) are the existing Shu–Osher `axpby` combinations.

## Module map

| Module | Purpose |
|---|---|
| [`NonuniformKernel`](../CFDLean/Exec/NonuniformKernel.lean) | `widthAt`, the first-order and MUSCL kernels, size lemmas |
| [`NonuniformRefinement`](../CFDLean/Exec/NonuniformRefinement.lean) | `meshOf`, index lemmas, the compatible-model stencil lemma, the alignment lemma; FVNA-F, FVNA-M, FVNA-U |
| [`NonuniformTransfer`](../CFDLean/Exec/NonuniformTransfer.lean) | Bridges between the array diagnostics and the periodic field; FVNA-T |
| [`NonuniformControls`](../CFDLean/Exec/NonuniformControls.lean) | Exact real controls FVN-BC and FVN-E through the kernels; empty input, `dt = 0`, one cell |
| [`NonuniformKernelSmoke`](../CFDLean/Exec/NonuniformKernelSmoke.lean) | `Float` smoke run on the control data (`#eval`, prints only) |
| [`FV1DNonuniformArrayChallenge`](../CFDLean/Verification/FV1DNonuniformArrayChallenge.lean) | Trusted FVNA-M and FVNA-T statements; Mathlib plus the hash-pinned kernel modules |
| [`FV1DNonuniformArrayVerify`](../CFDLean/Verification/FV1DNonuniformArrayVerify.lean) | 13 bridge theorems |
| [`Challenges/FV1DNonuniformArray.lean`](../Challenges/FV1DNonuniformArray.lean) | `lake comparator` challenge ([configuration](../Challenges/FV1DNonuniformArray.comparator.json)) |

## Representation

Array entry `i` represents periodic cell `(i : ZMod n)`. A field `u : ZMod n → S` is stored as the FVA
`samples u`; every array of size `n` is such a `samples` (`samples_entries`). `meshOf widths hw hpos` is the FVN
`Mesh1D` on `zmodGrid n` whose cell `j` has width `widthAt widths j.val`, which is `widths[j.val]` (`meshOf_width`);
it needs `widths.size = n` and positive entries. `nextIdx` and `prevIdx` are `next` and `prev` of `zmodGrid n` on the
residues (`natCast_nextIdx`, `natCast_prevIdx`), and they are inverse to each other (`nextIdx_prevIdx`,
`prevIdx_nextIdx`).

## Frozen result IDs

Names are in `CFDLean.Exec`.

| ID | Binding | Proof |
|---|---|---|
| FVNA-F | `burgers_nonuniform_refines`, `euler_nonuniform_refines` (`NonuniformRefinement`); supporting `nonuniformStepArray_compatible` | The supporting stencil lemma is stated only for a compatible model `⟨(· + ·), (· - ·), (· • ·), F, a⟩` over a real module, because the FVA `Model` record carries operations without laws. For it the kernel stores the FVN first-order step with the FV1D Rusanov face on `meshOf widths`: the kernel's predecessor read `i − 1` is `prev` on the residues and the update divides by the width of its own cell. The real Burgers and Euler models are equal to compatible models (private lemmas `burgers_model` and `euler_model`, as in the FVA refinement), which gives the two bound theorems. Euler keeps the contract's `γ > 1` and admissibility hypotheses although the proof does not use them. |
| FVNA-M | `nuLimiterEulerStepArray_refines`, `nuLimiterSsprk2StepArray_refines`, `nuLimiterSsprk3StepArray_refines` (`NonuniformRefinement`); supporting `nuFace_alignment` | Per cell, the rescaled kernel differences are the FVN differences `w i / δ` times the state difference (`two * w[i] / (w[i−1] + w[i])` is `w i / δ (i−1)` written without halving), so slopes and face states agree for every limiter, including `none`; no limiter case split. The face flux is the Rusanov flux, equal to the FVN Burgers face. SSPRK2 and SSPRK3 follow from Forward Euler and `axpby_samples`. |
| FVNA-U | `burgers_nonuniformStepArray_uniform`, `euler_nonuniformStepArray_uniform`, `nuLimiterEulerStepArray_uniform`, `nuLimiterSsprk2StepArray_uniform`, `nuLimiterSsprk3StepArray_uniform` (`NonuniformRefinement`); supporting `nonuniformStepArray_uniform` | With every width `dx`, `widthAt` reads `dx` and the first-order kernel is the FVA `stepArray` entry by entry, for every real model (the generic supporting lemma; the two bound theorems are its Burgers and Euler instances). For MUSCL both rescaling factors are `two * dx / (dx + dx) = 1`, so the slope arguments are the E0c differences; `limiterSlope` is never unfolded, so no limiter case split. FVNA-U needs no `n ≥ 1`: empty arrays are equal. |
| FVNA-T | (a) `burgers_nonuniformStepArray_weighted_sum`, `nuLimiterEulerStepArray_weighted_sum`, `nuLimiterSsprk2StepArray_weighted_sum`, `nuLimiterSsprk3StepArray_weighted_sum`, `euler_nonuniformStepArray_weighted_sum`; (b) `burgers_nonuniformStepArray_bounds`, `burgers_nonuniformStepArray_totalVariation_le`; (c) `run_nuLimiterEulerStepArray_stable`, `run_nuLimiterSsprk2StepArray_stable`, `run_nuLimiterSsprk3StepArray_stable` (`NonuniformTransfer`); supporting `represents_samples`, `entriesBetween_samples_iff`, `totalVariationArray_samples`, `weightedSumArray_samples`, `meshOf_meshRatio_iff` | Every size-`n` array is `samples U`; FVNA-F and FVNA-M turn each kernel into `samples (T U)`; the supporting bridges turn `sumArray (Array.zipWith (· * ·) widths u)`, `EntriesBetween` and `totalVariationArray` into the FVN weighted sum, bounded states and total variation on `meshOf widths`. Then (a) is FVN-C (`firstOrderStep_weighted_sum`, `musclStep_weighted_sum`; SSPRK2 and SSPRK3 keep the linear invariant because their coefficients sum to one), (b) is FVN-B, (c) is FVN-MB with `L.slopeBounded`. Euler (a) goes through the compatible-model stencil lemma, not through `euler_nonuniform_refines`, so it needs no admissibility. |

Definitions are bound under the ID that introduces them: `FV1D.nonuniformStepArray`, `widthAt` and `meshOf` under
FVNA-F; `nuBackDiff`, `nuFwdDiff`, `nuSlopeAt`, `nuLeftState`, `nuRightState`, `nuFaceFlux` and the three MUSCL
kernels under FVNA-M. The promised theorems are the 20 bound declarations; every other public lemma is supporting or
unbound.

**Alignment lemma.** `nuFace_alignment` states the face and width alignment, seam included, in one lemma: the
backward difference that the right cell `j + 1` uses at face `j` has the pair `w[j]`, `w[j+1]`, the spacing of face
`j` (from `prevIdx_nextIdx`); the right state at face `j` is the FVN right state at face `j`; and the right state at
face `j − 1`, which the kernel reads at `nextIdx (prevIdx j)`, is the FVN right state at face `prev j` (from
`nextIdx_prevIdx`). At `j = 0` the face `j − 1` is the seam face `n − 1`. The FVNA-M proofs use the per-face lemmas;
the alignment lemma states the same facts on their own, for review.

**Literal readings.**

- FVNA-M, FVNA-U and FVNA-T (a) do not assume `0 ≤ dt`: they are algebraic identities true for every real `dt`.
  FVNA-T (b) and (c) assume it, as FVN-B and FVN-MB do.
- FVNA-T (a) for Euler holds for every `γ` and every array, without admissibility, separately for the stored
  components `k = 0, 1, 2` (density, x-momentum, total energy, the order of `FV1D.EulerState` and `Euler1D.encode`).
- FVNA-T (b) writes the FVN-B conditions on the array: `a i = max |u[i]| |u[i+1]|` with `u[prevIdx i]` and
  `u[nextIdx i]`, and the widths as `widthAt widths i.val`. The trusted statements write the widths as `widths[i]`;
  the bridges rewrite one into the other in range (`widthAt_of_lt`).
- FVNA-T (c) "`n` steps" means any number of steps: the theorems hold for `run step k u` for every `k`, which
  includes `k = n` (`n` also names the cell count). The mesh ratio is stated on `meshOf widths`, as in the contract;
  `meshOf_meshRatio_iff` gives the array form `θ * max widths[i] widths[i+1] ≤ widths[i] + widths[i+1]` used by the
  trusted statements. FVNA-T (c) inherits the FVN finding: minmod works on any mesh, van Albada needs neighbour widths
  within a factor of 4, and MC, superbee and van Leer need equal neighbour widths.
- FVNA-T (a) is one step, as in the contract ("keeps").

## Trusted boundary

FVNA-M and FVNA-T are restated in a trusted file that imports Mathlib and, as for E0c, the hash-pinned kernel modules
and real instances (`trusted_inputs` in `scripts/verify.py`): `Kernel`, `RealScalar`, `MusclKernel`,
`LimiterKernel`, `RealScalarSign`, `FV1D` and `NonuniformKernel`. Everything else (the limiter slopes in classical
form, the FVN MUSCL step on `ZMod n`, SSPRK2 and SSPRK3, `Represents`, `EntriesBetween`, the mesh ratio of a width
array) is restated from Mathlib. FVNA-F and FVNA-U are checked by the verifier and the kernel audit only, as for FVA.

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
|---|---|---|---|
| FVNA-M | `MusclEulerStepRefines`, `MusclSSPRK2StepRefines`, `MusclSSPRK3StepRefines` | `muscl_*_step_refines` | `nuLimiter*StepArray_refines` |
| FVNA-T (a) | `FirstOrderWeightedSum`, `MusclEulerWeightedSum`, `MusclSSPRK2WeightedSum`, `MusclSSPRK3WeightedSum`, `EulerFirstOrderWeightedSum` | `first_order_weighted_sum`, `muscl_*_weighted_sum`, `euler_first_order_weighted_sum` | `burgers_nonuniformStepArray_weighted_sum`, `nuLimiter*StepArray_weighted_sum`, `euler_nonuniformStepArray_weighted_sum` |
| FVNA-T (b) | `FirstOrderBounds`, `FirstOrderTotalVariation` | `first_order_bounds`, `first_order_total_variation` | `burgers_nonuniformStepArray_bounds`, `burgers_nonuniformStepArray_totalVariation_le` |
| FVNA-T (c) | `MusclEulerRunStable`, `MusclSSPRK2RunStable`, `MusclSSPRK3RunStable` | `muscl_*_run_stable` | `run_nuLimiter*StepArray_stable` |

The [statement review](../reviews/FVNA/TrustedStatements_Review.md) by a separate AI agent found no mandatory issue
and accepted the deliberate choices above. Its non-blocking remarks: (1) the trusted file could name the E0
statements `SumDiagnostic` and `TotalVariationDiagnostic` where it relies on `sumArray` and `totalVariationArray`;
(2) `weightedSum` uses `Array.zipWith`, which truncates to the shorter array, harmless because every statement assumes
equal sizes; (3) FVNA-T (c) "`n` steps" means any number of steps (recorded above and in the catalog); (4) no
array-level `run` refinement is stated, and the contract asks for none. Remarks (1) and (2) would change the trusted
file and are not applied, so the reviewed hash stays valid. No human has reviewed the trusted statements yet.

## Exact controls

All values are exact rationals from the contract. Each control is a separate declaration in
[`NonuniformControls`](../CFDLean/Exec/NonuniformControls.lean), obtained from the FVN controls through FVNA-F and
FVNA-M on `meshOf widths`. Controls are not bound; they are checked by the `--wfail` build and the kernel audit.

- **FVN-BC** (Burgers). Widths `(1, 3, 1, 1)`, state `(0, 1, 6/5, 0)`, `dt = 1/10`: first order
  `(1/40, 1463/1500, 1141/1000, 27/250)` (`burgers_firstOrder_fvnBC`) and minmod MUSCL Forward Euler
  `(289/16000, 23327/24000, 18529/16000, 27/250)` (`burgers_minmod_fvnBC`). Cells 0 and 3 read the seam face, so a
  wrong width or state pairing there changes the values.
- **FVN-E** (Euler, `γ = 2`). Widths `(1, 2, 1)`, `dt = 1/16`, states `(ρ, ρ, 2 + ρ/2)` for `ρ = 1, 4, 9`: densities
  `(35/16, 249/64, 257/32)`, momenta equal to the densities, energies `(99/32, 505/128, 385/64)`
  (`euler_firstOrder_fvnE`).
- **Edges.** An empty input gives an empty output for every arithmetic and every kernel (`*_empty`; outside the
  physical theorems, no indexing). `dt = 0` (`*_dt_zero`) and one cell, where the seam reads the cell itself
  (`*_one_cell`), give the identity for every kernel.

**Native smoke test.** [`NonuniformKernelSmoke`](../CFDLean/Exec/NonuniformKernelSmoke.lean) runs every kernel in
`Float` on the edges and on the FVN-BC and FVN-E data with `#eval`. It prints the outputs and proves nothing: `Float`
results are outside the exact-real proof boundary, and `Float` error bounds belong to E1. The module is imported by
`CFDLean.lean`, so every build shows its output as information messages.

## Checks

`scripts/verify.py` (result map, axioms, trusted file, challenge and `trusted_inputs` hashes, bridge types),
`KernelAudit.lean`, `StatementChecks.lean` (one example per promised theorem), the in-file checks of the refinement
and transfer modules (every public theorem instantiated with one cell), the `--wfail` builds of the controls, smoke
and bridge modules in CI, and `lake comparator --paranoid --config Challenges/FV1DNonuniformArray.comparator.json`.

## Exclusions

No driver change: a non-uniform mesh option belongs to the planned general driver `fv1d --model burgers|euler`. No
`Float` error bound (E1), no Euler MUSCL, no Euler positivity on the non-uniform mesh and no mesh-adapted limiter.
