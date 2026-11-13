# Reviewer prompt: M3 scientific proposal

Please independently review the **M3 proposal only** in the private repository `rois1995/CFD_Lean` at revision **`b0e5d1405082c1058d2a55ecb273e2404d135005`**:

[Proposed scientific specification](https://github.com/rois1995/CFD_Lean/blob/b0e5d1405082c1058d2a55ecb273e2404d135005/specifications/M3-proposal.md) · [scope and preparation evidence](https://github.com/rois1995/CFD_Lean/blob/b0e5d1405082c1058d2a55ecb273e2404d135005/reviews/M3/README.md).

Full M2 is independently accepted at mathematical revision `ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`, with no blockers or conditions. The proposal checkpoint records both the M2d and composed-M2 decisions and preserves all original independent evidence. Verify that closeout is faithful; no accepted Lean source, frozen contract, dependency pin, audit/checker script or deterministic audit output should have changed.

Review the proposed outgoing node-centered residual, paired incidence, actual accepted M2 Roe specialization, exterior-patch ownership, global boundary-balance identity and orientation/reindexing invariance. Check that constant-state preservation requires both the correct geometric closure and explicitly compatible supplied boundary fluxes.

Review the concrete tetrahedral barycentric median-dual construction: all 24 flag tetrahedra, six-per-vertex grouping, outward interface triangles, primal-face patches, shared-face cancellation, derived local/global area closure, determinant volumes and used-node positivity. Closure and volume partition must be proved, not inserted as input certificates. Identify missing domain or conformity assumptions.

Assess the explicit choice to sum oriented partial-face vectors first and evaluate one original Roe flux using direct nodal states. Distinguish its Euclidean vector magnitude from the sum of facet areas, and distinguish this scheme from summing nonlinear Roe fluxes over nonparallel facets. Review the documented Blazek p. 142 normalization ambiguity and the proposed project convention; no authenticated erratum or second-order accuracy is claimed.

Check the six proposed result IDs, two-stage plan, exact rational preparation controls and extension of inheritance/audit guards to all 66 accepted M2 contracts before implementation. Treat preparation checks as design controls, not Lean proofs. No M3 Lean implementation has begun.

Return a proposal verdict recommending approval, amendment or rejection; identify blocking/nonblocking findings with file references; and state the concrete decisions Andrea must make before authorizing M3 implementation. This proposal review itself must not authorize implementation or reopen accepted M2 without a specific justified finding. Boundary algorithms, time updates, mixed-element extensions, entropy/positivity repairs and SU2 correspondence remain outside this proposal.
