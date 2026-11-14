# Independent M3b and full-M3 review

**M3b verdict — Accept M3-G/V and concrete M3-C. No blockers or outstanding conditions.**

**Composed full-M3 verdict — Accept I/R/O/G/V/C within the approved exact-real tetrahedral scope. No blockers or outstanding conditions.**

Candidate `e2ea538b8da38c01c098ef28a3ea31030d90c6bb`, tree `1cf0e361d9b2a323ac23f6f129d26fb3599ec00b`. Handoff checkpoint `6284949a428e6a6e12fbe98ad21a5b2a10778cfe`. Accepted M3a baseline `a70270c3f771e66bcaaebc18b8480c32f9606b1e`; M2 pin `ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`; M3 scientific/representation freeze `3189a603b3f6af953f0828d6b2e239320fd2cd20`.

## Concrete construction and hypotheses

`CFDLean/Geometry/MedianDual/Mesh.lean` defines MeshData with actual finite node coordinates, injective four-node cell maps and positive determinants. The positive-order restriction represents every nondegenerate tetrahedron after reordering, as proved by Local.nonzero_has_positive_order. Conforming adds unique cell vertex sets, coordinate injectivity on Used nodes, the exact convex-hull intersection through shared node IDs, computed face multiplicity at most two and the geometric opposite-side condition. Faces and occurrences are computed from vertex membership. No closure, volume partition, cancellation or residual certificate is an input. The orientation condition is a dot product against a geometrically defined outward face vector, with a separate theorem proving the own opposite vertex has negative sign. It is a legitimate side-of-plane assumption.

Stronger public closure/volume statements retain Conforming; several algebraic helpers require fewer hypotheses. In particular volume partition follows from finite flag and node sums without embedding, and local vector closure is a polynomial identity even on degenerate points. Those stronger algebraic types add no physical interpretation for invalid meshes. Mesh parsing and validation remain outside the result.

## M3-G findings

In Local.lean, `flagPoints`, `valid`, `frameSign`, `flagBoundary`, `outwardTriangle`, `localInterface` and `localPatch` define the actual barycentric geometry. `flag_card` and `vertexFlags_card` count 24 flags and six at each node. The orientation sign tracks permutation parity; it is not a normal certificate supplied by a caller. `outwardTriangle_dot` proves the edge-direction dot product is sixVolume/24. MeshData.positive therefore makes every relevant triangle outward and nonzero.

`internal_face_one_pair` and `internal_face_two_pair` give explicit j/k and k/l cancellations. Their fixed-point-free involutions sum the internal flag faces to zero. `flag_boundaries_identify` and `localHull_identification` identify the surviving face vectors with the specified interfaces and primal-face patches. `local_closure` follows from this face-boundary chain. The closed formulas `localInterface_eq` and `localPatch_eq` are proved from their explicit triangle sums; two scoped maxHeartbeats increases expand the available elaboration budget without changing axioms or kernel checking.

Mesh.lean's `faceArea_eq_or_neg` derives triangle equality up to sign from equal unordered node triples. `faceArea_cancel_of_side` uses the genuine opposite-side condition to select the negative sign. `faceArea_cancel` consequently derives shared-face cancellation. No cancellation conclusion appears in Conforming.

Edges.lean's `Edge` is the subtype of increasing distinct node pairs co-occurring in a cell. `assembledArea` sums the local oriented triangles over actual matching cell-node IDs. `edge_incidence_sum` compresses antisymmetric supported rows to one record per unordered edge; self and unsupported terms are proved zero. The numerical flux is absent from this area summation.

Boundary.lean's exterior records retain the cell/omitted-face occurrence and owner node, with computed count one and actual face membership. `boundaryKey_injective` and `boundaryKey_range` prove exact exterior face/node ownership multiplicity. `ownedPatch_local` identifies its one-third primal-face vector with the two local barycentric triangles. `face_other`, `partner_ne` and `partner_involutive` construct and pair the two actual interior occurrences. `interior_cancel` and `all_patches_boundary` leave precisely the exterior records.

MedianDual.lean's `interfaces` uses these exact Edge and Boundary types. `metric_closed` composes edge incidence, local closure and interior/exterior patch reduction on these same edgeArea/boundaryArea vectors. No separately assumed metric certificate is substituted. `roe_boundary_balance` uses accepted Assembly.roeTransfer with the already aggregated area vector and arbitrary exterior data, deriving global boundary balance through the accepted M3a theorem. There is one Roe evaluation per aggregated edge and no extra area multiplier.

## M3-V and concrete M3-C findings

`flag_determinant` and `flag_volume` derive the frame-signed determinant ratio and absolute Vol(T)/24 for every valid flag. `localDualVolume_eq` sums the six actual flag volumes to Vol(T)/4. `dualVolume_formula` derives the sum over incident primal cells by their actual node identity; `dualVolume_pos` needs Used and a positive incident determinant; `dualVolume_unused` gives zero on unused nodes. `volume_partition` derives the total determinant-volume identity. The scope remains finite subdivision and determinant sums, with no asserted measure of a geometric union.

`MeshData.constant_state` applies the accepted Assembly.constant_state_closed to the derived metric_closed on the exact same interfaces/areas. Supplied exterior data are explicitly the actual physicalTransfer at the same common state. Its raw algebraic type is stronger than the approved physical specialization; gamma>1 and admissibility suffice for that specialization. Arbitrary future boundary algorithms are not asserted compatible.

Controls.lean supplies standard and genuinely oblique one-cell conforming examples, valid-flag/all-node controls, unused-node zero and explicit degenerate/nonmanifold exclusion implications. Its actual admissible resting state has compatible zero residual; a one-patch perturbation yields a nonzero actual Roe residual. TwoCells.lean proves the full Conforming predicate, including a genuine convex-hull intersection argument for [0,1,2,3] and [0,2,1,4]. Its shared patches cancel, edge 01 area is (1/6,1/12,0), shared-node volumes are 1/12, apex volumes are 1/24, and the total is 1/3.

RoeAggregation.lean proves the approved nonparallel counterexample with actual accepted projectors and Roe flux. Its cold/hot conservative energies 1 and 4 at gamma=2 and density one give pressures 1 and 4. `mass_formula` is -3 sqrt(5)|S|/10, equal to -3|S|/(2sqrt(5)). `nonparallel_not_additive` exhibits the difference between the single (1,1,0) evaluation and summed coordinate-axis evaluations. No facetwise nonlinear equivalence is used in the construction.

## Preservation and audit

All 84 accepted types and mathematical definition/proof files, including Assembly.lean, match the accepted M3a Git blobs. M1/M2/M3 scientific contracts, representation companion, M2 binding map, Integrity.lean, KernelAudit.lean and compiler/dependency pins are preserved. The 73 previous examples form an exact unchanged prefix. The full-index Git diff from accepted M3a matches the checkpoint's Changes_from_Accepted_M3a.patch byte for byte.

The guard now pins accepted M3a. `check_m3_inherited` freezes all active M3a parts, their ordered bindings/stages and types, alongside the M2 inheritance guard and accepted module source hashes. This closes the M3a review's next-stage finding. The scientific metadata/layout and two C parts remain frozen independently. All 33 new M3b bindings are mapped, giving 117 cumulative bindings and no deferred M3 parts.

KernelAudit.lean is unchanged and covers owning-module declarations including generated names. Unsafe compiler/executable auxiliaries and metadata-only declarations remain visible as non-roots. A safe mathematical root must pass both permitted-axiom and transitive unsafe-reachability checks. Skipping per-root axiom queries on unsafe compiler records supplies no executable verification claim. Separate reviewer traversal and fresh comparison are recorded below.

## Composition and next steps

Full M3 is the composition of the preserved I/R/O/conditional-C assembly with the new derived G/V/concrete-C construction. It establishes the outgoing residual boundary balance, orientation/relabeling interfaces, exact metric closure, determinant-volume identities and common-state preservation with compatible boundary data for the approved tetrahedral, direct-state, edge-aggregated original Roe scheme.

After recording separate M3b and full-M3 decisions, retain this immutable mathematical pin and independent evidence. Any future milestone must preserve all accepted M2/M3 bindings and sources. The next decision is a separately reviewed M4 boundary proposal, with exact variant/domain and compatibility requirements; this review starts no M4 implementation. Time stepping, entropy/update-positivity repairs, mixed cells, mesh parsing, floating-point behavior and SU2 correspondence remain outside this checkpoint.

## Independent fresh-source reproduction

The uploaded handoff checksums passed. The complete Git bundle was cloned and the exact candidate/tree authenticated against the connected repository, together with checkpoint 6284949. Starting from a clean detached candidate without .lake, I ran scripts/reproduce.sh unchanged. Workspace maintenance had removed the previous compiler, so I downloaded the official Lean 4.19.0 Linux release from leanprover/lean4, checked its version/commit and retained the download digest. The replay used LEAN_NUM_THREADS=8. Nine manifest-pinned dependencies were fetched afresh, both binary-cache controls were enabled and pinned widget assets were compiled locally.

The procedure exited 0. The cold build, 12 checker fixtures, 112 Lean examples and all 49 source hashes before/after regeneration passed. All five deterministic outputs matched both the candidate Git blobs and the submitted checkpoint archive byte for byte. The worker archive hashes also passed independently. Only evidence/build.log differed in the tracked checkout.

The reproduced audit inventories 1,356 records and all 117 promised bindings, with 84 inherited types checked and no deferred M3 part. It retains 353 unsafe non-roots (318 definitions, 35 compiler axiom records) and 223 metadata-only records. A separately implemented reviewer traversal of types, values, constructors and recursor rules reached 20,935 declarations from 780 safe roots. It found precisely propext, Classical.choice and Quot.sound and no reachable unsafe declaration. The reviewer Lean file passed with warnings treated as errors. It composes outward-triangle positivity with MeshData.positive, common-state preservation with positive used-node volumes/partition, and the nonparallel counterexample with the public numericalFlux encoding. Earlier reviewer physical-flux/secant/assembly composition controls also pass.

Independent symbolic checks verified the general flag determinant ratio and triangle dot-product coefficient, all 48 flags of the two-cell example, its aggregated edge 01 vector and the total nodal volume. These are supplementary checks alongside general Lean proofs. All replay and reviewer work occurred in an isolated local checkout; the remote repository was not modified.
