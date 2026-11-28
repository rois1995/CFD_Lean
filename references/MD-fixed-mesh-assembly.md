# Fixed-mesh conservative assembly proof map

The [frozen proposal](../specifications/MD-fixed-mesh-assembly-proposal.md) and [independent decision](../reviews/MD/Assembly_Contract_Freeze.md)
fix the hypotheses. All names below are in `CFDLean.FixedMesh`. The [implementation](../CFDLean/Discrete/FixedMesh.lean)
uses `Assembly.Interfaces` for topology and takes the field, cell measures, fluxes and area vectors as separate functions.

| ID | Declarations to review | What to check |
|---|---|---|
| MD-C | `interior_owner`, `interior_neighbor`, `interior_other`, `global_balance` | One oriented value per interior face. Check the signs at both named cells. Summing over cells leaves the boundary sum for arbitrary additive commutative groups. |
| MD-K | `constant_defect`, `constant_residual` | The interior consistency and boundary compatibility assumptions identify both transfers with the same linear map. Cell closure then gives zero. |
| MD-U | `step_balance`, `step_zero`, `step_zero_residual` | Multiply by each cell's positive volume to recover its outward transfer at the common timestep. The final balance invokes MD-C. |

Supporting lemmas give empty-boundary conservation (`closed_balance`, `step_closed`), orientation reversal
(`residual_reverse`) and agreement with the accepted vector assembler (`coordinates_agree`). No mesh record or physics
adapter is needed for these results. Reindexing is scheduled with the geometry extraction after the second scalar mesh.

The [new control](../benchmarks/ReviewCases/FixedMeshAssembly.lean) constructs the oblique and exterior transfers from the
coordinates and upwind rule in the [independent rational control](../benchmarks/ReviewCases/OrientedTriangles.lean).
It applies the generic assembly and update and checks both cells against `(4,17)` and `(3/2,63/16)`. A duplicated face
or exchanged incidence can pass the sum check while failing these endpoint comparisons.
