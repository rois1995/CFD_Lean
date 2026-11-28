# First-order scalar advection proof map

The [fixed-velocity contract](../specifications/MD-scalar-advection-proposal.md) was [independently frozen](../reviews/SA/Contract_Freeze.md).
All production declarations below are in `CFDLean.ScalarAdvection`. Geometry and cell data enter as functions over
the accepted interface topology. The outward boundary realization accepts a prescribed exterior mean independently
on each boundary face. [Source](../CFDLean/Schemes/ScalarAdvection.lean)

| ID | Declarations | Review focus |
|---|---|---|
| SA-F | `flux_consistent`, `flux_reverse`, `flux_zero_speed` | The signed speed includes face measure. Check state swap at negative speed and exact zero flux for tangential transport. |
| SA-K | `constant_residual`, `constant_step` | Apply the same linear physical transfer to owner-oriented and exterior vectors. Invoke `FixedMesh.constant_residual` and then `FixedMesh.step_zero_residual`. |
| SA-C | `global_balance`, `step_balance`, `step_closed` | Both face functions feed `FixedMesh.residual`. The global results specialize MD-C and MD-U for arbitrary prescribed exterior means. |

The [exact controls](../benchmarks/ReviewCases/ScalarAdvection.lean) call the production interior and boundary fluxes.
The triangle reconstructs area vectors from the original vertices and uses both unequal areas. The patch uses four
interior faces, eight exterior edges, and both signs of the transport speed. Each control checks geometric closure,
cell residuals, updated means and integrated boundary exchange. The scalar adapter uses exact reals. Reindexing,
geometry extraction, executable arrays, Euler, multidimensional reconstruction and machine-error claims have later scopes.
