# Proposal for first-order scalar advection on a fixed mesh

**Decision requested.** Freeze SA-F, SA-K and SA-C for the first physics adapter over the
[fixed-mesh assembly](../references/MD-fixed-mesh-assembly.md). Parent on the implementation branch is
`b34ddff559bb614e8f94b27742d37e43f2ee47da`. Independent review of this proposal precedes scientific implementation.

## Face contract

Fix a velocity `v` throughout the mesh and the step. For an oriented face area vector `A` in `Fin d → ℝ`, let
`s = Σ j, v j * A j`. The physical integrated flux at cell mean `u` is `s * u`. First-order traces on an interior
face are the owner mean `l` and neighbor mean `r`. Define `H(l,r,A) = s * (if 0 ≤ s then l else r)`. The owner
computes this flux once. On an exterior face use the owner and a supplied exterior mean in the same formula with
the outward boundary vector. This implements prescribed inflow and uses the interior state at outflow. A face with
zero speed carries exactly zero transfer, irrespective of both states. No normal normalization or global width is needed.

| Claim | Statement and proof map |
|---|---|
| SA-F | Consistency `H(k,k,A) = (v·A) k` and reversal `H(r,l,−A) = −H(l,r,A)`. Derive the sign flip from linearity in `A` and check zero speed in the sign split. |
| SA-K | For constant interior and exterior means `k` and cellwise geometric closure, the cell residual is zero and a Forward Euler step preserves `k`. Supply `A ↦ (v·A) k` to `FixedMesh.constant_residual`, then apply `step_zero_residual`. |
| SA-C | With arbitrary prescribed exterior data, the global residual equals the realized boundary sum. Positive fixed cell measures and one common timestep give a change in total amount of `−dt Σ b, H_b`. On an empty boundary this is zero. Specialize `FixedMesh.global_balance` and `step_balance` directly. |

## Exact control on unequal triangles

Use the frozen [two-triangle data](FV2D-oriented-face-proposal.md) and the [independent rational control](../benchmarks/ReviewCases/OrientedTriangles.lean).
The new physics adapter must produce the same oriented shared transfer `6`, cell residuals `(4,17)`, updated means
`(3/2,63/16)` and boundary rate `21` as the parent assembly control. Exercise the real production face function on
the oblique area vector, both orders of the shared states, and the four boundary vectors.

## Exact control on a four-cell Cartesian patch

Tile `[0,2] × [0,2]` by unit squares. Order the cells SW, SE, NW, NE with means `1,3,2,4`. Set `v=(2,−1)`,
exterior mean `0` on every outer face and `dt=1/8`. The internal face measures are one. Orient internal faces east
or north and use the outward unit area vector on each of the eight boundary faces. The eastward and northward faces
exercise opposite upwind branches with the same orientation convention.

| Interior orientation | SW → SE | NW → NE | SW → NW | SE → NE |
|---|---:|---:|---:|---:|
| `v·A` | 2 | 2 | −1 | −1 |
| Integrated transfer | 2 | 4 | −2 | −4 |

| Quantity | SW | SE | NW | NE |
|---|---:|---:|---:|---:|
| Sum of outward boundary transfers | 1 | 9 | 0 | 8 |
| Residual including shared faces | 1 | 3 | 6 | 8 |
| Updated mean | 7/8 | 21/8 | 5/4 | 3 |

The initial amount is `10`, the boundary rate is `18`, and the final amount is `31/4`. Compare every shared transfer
and cell as well as the total. For the independent constant control, set all interior and exterior means to the same
`k` and check each cell's outward area vectors sum to zero. Both examples must call the same physics adapter and
assembler. The existing [two-triangle generic control](../benchmarks/ReviewCases/FixedMeshAssembly.lean) supplies
an independent comparison for the first mesh.

The implementation supplies a face-flux adapter and both mesh instances. Reindexing and the common geometry record
follow comparison of the two instances. Executable arrays, Euler, higher-order reconstruction, time-accuracy claims,
multidimensional CFL bounds and machine-arithmetic certification require later work.
