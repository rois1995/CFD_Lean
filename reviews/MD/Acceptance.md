# Independent implementation acceptance of fixed-mesh assembly

The external reviewer approved MD-C, MD-K and MD-U in [PR #75](https://github.com/rois1995/CFD_Lean/pull/75)
at `3ee5d90a4c18ca5fa50ce6f3677fed9eee1b932f` against `develop` at `f0e87e7edd4fd6a3390a8ca861259b10ff305dc5`.
The verdict was “APPROVE PR #75 for implementation acceptance.” The reviewer requested no mandatory changes.
The [contract freeze](Assembly_Contract_Freeze.md) and [implementation proof map](../../references/MD-fixed-mesh-assembly.md)
identify the agreed hypotheses and supporting lemmas.

| Claim | Accepted declarations in `CFDLean.FixedMesh` | What the reviewer confirmed |
|---|---|---|
| MD-C | `global_balance` | One integrated transfer per interior face contributes with opposite signs at the owner and neighbor. Summing over cells leaves the realized boundary transfers. |
| MD-K | `constant_defect`, `constant_residual` | Interior and boundary transfers must agree with the same linear map. Applying it to a closed cell's area-vector sum yields zero residual. |
| MD-U | `step_balance` | Multiplication by each cell's own positive measure cancels its local denominator. The weighted global balance then follows from MD-C. |

The two-triangle control recovered the cell residuals `(4,17)` and the updated means `(3/2,63/16)` through the new
assembler. The review confirmed the 617 preserved parent type pins, four new declaration pins and successful
[Integration CI on the reviewed head](https://github.com/rois1995/CFD_Lean/actions/runs/46139241875).
Named checks for the boundary sum and total amount, and a named composition of constant residual with the time update,
were optional suggestions. The next scientific decision is the independent freeze of [the scalar upwind proposal](https://github.com/rois1995/CFD_Lean/pull/76).
