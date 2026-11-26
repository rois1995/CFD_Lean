# FV1D follow-up proposal — one shared array step and its exact-real refinement

**Proposed for independent review.** The mathematical reference is the [frozen FV1D step](FV1D.md) and
[PR #26 implementation candidate](https://github.com/rois1995/CFD_Lean/tree/c8a964e35a4b34a95fa50d2e43b4b036a0e4af38).
The intended deliverable is an executable Lean library kernel that advances **one selected model** by one
first-order step. A driver can later expose it through `fv1d --model`.

## Kernel and representation

One traversal takes the old `Array S`, coefficients `dx dt : α`, a physical flux `S → S`, and a face
speed `S → S → α`. The common face uses state addition and subtraction and scalar multiplication
`α → S → S`. Compute each output from the two periodic faces of the old array. Reuse the proof-carrying
[successor and predecessor indices](../CFDLean/Exec/Kernel.lean). For an empty input the array construction
returns an empty output without indexing. The physical grid has positive size.

Use the existing scalar arithmetic where it supplies the coefficient operations. For Burgers the stored
state is a coefficient. For Euler it is the triple of density, x-momentum and total energy over that
coefficient type. Supply square root to the Euler endpoint speed alone. For the exact-real interpretation,
connect the executable pressure, positive-x flux and endpoint speed to the existing M1/FV1D definitions.
No equation-name branch is needed in the traversal. Preserve the current `burgers1d` options, defaults and
kernel entry points, including its SSPRK3 driver.

## Proposed claims

Let `n ≥ 1`, `i : Fin n`, `dx > 0` and `dt ≥ 0`. Interpret executable coefficient operations as their
real counterparts. Array entry `i` represents periodic cell `(i.val : ZMod n)`. For Euler, representation
asserts equality to the three M1 components in that order. Advancement preserves the array size.

| ID | Statement |
|---|---|
| FVA-B | For every real input array of size `n`, the Burgers instance of the shared array step agrees entrywise with the assembled B0 Forward Euler step on the represented periodic field. It also equals the existing `CFDLean.Exec.eulerStepArray dx dt` on the same input over the reals. |
| FVA-E | For every `γ > 1` and every array representing an initially M1-admissible Euler field, the Euler instance produces an array representing `CFDLean.Euler1D.step γ dx dt U` at each cell. Equality covers all three components. |

Prove the indexing correspondence once, using the [E0 representation and refinement lemmas](../CFDLean/Exec/Refinement.lean)
where their types apply. Use the shared FV1D face formula in both instances. The Euler glue must account for
`p = (γ−1)(E−m²/(2ρ))`, the positive unit face, and the maximum endpoint speed. Reading through the
periodic seam must work for `n = 1`; `dt = 0` must preserve all entries.

FVA-E compares two one-step outputs. It needs neither a positivity CFL nor an admissible-output premise.
Once the separate positivity result is available, entrywise refinement can transfer that result to the real
array under its CFL hypotheses. That transfer is a subsequent claim.

## Execution controls and review boundary

- On the [three-cell Euler control](FV1D.md#exact-control-for-the-euler-step), check the real array shape and all
  nine expected output components. Check Burgers agreement against the E0 array step on a nonconstant state.
- Exercise a singleton, an empty input and zero timestep. Keep the empty-array behavior separate from the physical
  periodic-grid theorem.
- Exercise both concrete model instances in native arithmetic as a smoke test. The theorem relates the kernel
  instantiated over the reals to FV1D. Native rounding-error bounds belong to E1.
- The model-selecting CLI, repeated steps, timestep policy, MUSCL and SSP integration have separate acceptance
  questions. This proposal leaves them for the driver and later numerical milestones.

**Review decision requested.** Check that the same kernel implements both steps, the `Fin` to `ZMod` mapping
preserves both neighbors, and the Euler model inputs refine M1. Recommend freezing FVA-B and FVA-E or give
mandatory changes.
