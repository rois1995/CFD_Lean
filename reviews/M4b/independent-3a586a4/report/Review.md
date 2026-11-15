# Independent M4b and composed full-M4 review

**M4b R/O/C verdict: ACCEPT without conditions.**

**Composed full M4 B/W/P/R/O/C verdict: ACCEPT without conditions.**

No blocking or conditional findings. Acceptance is limited to the approved mathematical scope and the exact candidate below.

Candidate `3a586a42546cba1784cc79269e3f9d1c5d843f0c`, tree `670a0ff21ce84187b04547b30ba27530983209aa`. Handoff checkpoint `416518f0961dbec4d26661c3fb8ff605b2db8830`. Accepted M4a baseline `37c1e6ee4618b0183135c2795b3aa6ebea2f22d5`; accepted M3 `e2ea538b8da38c01c098ef28a3ea31030d90c6bb`; M4 approval/freeze `0cff4af244b85f4e2071e7bf941d40fdd0a399b5`.

## Actual selected residual and M4-R

All new scientific interface names below have prefix CFDLean.Boundary in CFDLean/Boundary/Assembly.lean.

constructedTransfer calls the accepted transfer with the actual owner state, kind, exterior value and outward integrated area. stationaryResidual feeds this exact function to the unchanged Assembly.residual and accepted interior roeTransfer. meshResidual supplies the same accepted concrete interfaces, edgeArea and boundaryArea and derives the patch kinds/exterior values from the accepted primal-face maps. meshResidual_eq is a definitional identification with the accepted patchTransfer. There is no second area multiplier, new geometry, volume division or time step.

stationary_global_balance applies the accepted Roe boundary balance. stationary_mixed_balance separates the actual prescribed-exterior and pressure-traction contributions. stationary_component_balance, stationary_mass_balance, stationary_energy_balance and stationary_momentum_balance project the same conserved-vector layout. Mass and energy omit both traction kinds, while momentum retains each owner's actual pressure times T. The Fin 3 to Fin 5 momentum-index conversion is correct. mesh_global_balance specializes this same constructed rule on the concrete mesh.

These are valid stronger raw-state algebraic identities. Physical use still requires common gamma>1, admissible used-node states and admissible exterior data on prescribed faces. No general zero total momentum or update admissibility follows. The exterior data remain unused by wall/symmetry traction.

## Derived transport and M4-O

constructed_transfer_reindex derives pointwise transport by pushing the owner forward and pulling back kind, prescribed state, nodal state and area through the corresponding equivalences. It assumes no supplied transfer-transport certificate. stationary_residual_reindex first derives that constructed boundary-function equality and then invokes the accepted interior-Roe residual transport theorem. mesh_residual_reindex instantiates it with the actual face-derived patch data and accepted geometric area values.

The theorem quantifies over node, edge and boundary equivalences and transports every input. Its concrete instance transports an already constructed interface representation. Naturality of rebuilding a separately renumbered geometric mesh remains outside the approved statement. The numerical control swaps actual nodes, edge records and wall/open boundary records, transports nonconstant exterior data and moves a nonzero residual, so it tests more than an edge-loop permutation or an identically zero vector.

## Qualified compatibility and M4-C

transfer_compatible proves the actual selected branch is physicalTransfer using the preserved M4a wall iff for each traction label and actual Roe consistency for matching exterior data. stationary_common_defect derives the actual physicalFlux on the same metric defect. stationary_common_closed explicitly takes zero defect as its generic hypothesis.

The public mesh_constant_state retains Conforming, gamma>1, actual M1 admissibility, per-traction dot(momentum,T)=0 and matching prescribed data. It supplies the missing metric identity using accepted M.metric_closed for the very same interfaces and areas. Its unused physical hypotheses reflect a stronger algebraic helper; their presence in the public physical theorem is appropriate. Matching exterior data are a sufficient criterion, with no unnecessary iff claim.

residual_boundary_difference is a proved finite-sum identity. stationary_common_correction and mesh_common_correction apply it to the actual selected g and actual physical boundary transfer. They express the original residual as its physical metric term plus selected-minus-physical boundary discrepancies. They do not alter the numerical flux, insert a correction into the algorithm or assume a desired residual vector.

## Exact controls and nonempty physical cases

Boundary/AssemblyControls.lean uses the accepted standard, oblique and conforming two-cell meshes. standard_mixed_common covers every moving(q,1) state tangent to its wall. standard_all_wall_rest and oblique_all_symmetry_rest retain arbitrary unused exterior values. two_cell_common uses the actual [0,1,2,3]/[0,2,1,4] geometry, the derived face maps and a moving common state tangent to its two traction faces. two_cell_corner has one actual owner with wall, symmetry and prescribed kinds on three distinct primal faces. The two traction faces happen to be coplanar; the general theorem independently covers arbitrary conforming face geometry with its stated per-patch conditions.

The all-wall mass/energy balance controls hold for arbitrary nodal states on that mesh, and varyingStates supplies an explicitly admissible nonconstant-pressure family. pressure_force_retained gives (0,1,0,0,0) on an explicitly abstract interface. It illustrates retained pressure momentum without asserting that this abstract interface is a closed geometric control volume or that uniform pressure on a closed body has a nonzero net force.

incompatible_wall_residual evaluates the real selected rule at rho=1, momentum=(0,0,1), E=3/2, gamma=2. Matching exterior states leave the wall tangency failure, and the owner-0 residual is (1/6,0,0,1/6,5/12). The vector follows from the missing wall advective mass/momentum/energy contributions on T=(0,0,-1/6).

negative_axis_flux computes the genuine accepted Roe flux at the reversed normal, using the accepted absolute-operator reversal and projectors. mismatchingData is a function of actual primal-face identity, assigning pressure 3 on one open face and pressure 1 elsewhere; all values are admissible. incompatible_exterior_residual gives (-1/12,-1/6,0,0,-1/3) at owner 0. The proof uses one-sixth of that actual negative-axis Roe transfer, subtracts the physical common-state transfer, and proves every other face compatible. single_face_correction uses the accepted unique face/owner record to isolate this actual discrepancy, without an oracle for the residual.

transported_nonzero performs simultaneous nontrivial node/edge/boundary swaps with transported kinds, nonconstant exterior data and all area values. The same nonzero vector appears at node 1. Nodal states are constant in this numerical control, while the generic transport theorem covers arbitrary nodal states explicitly.

## Preservation, freeze and audits

The preimplementation inheritance extension at 4c0a4d554ba44b03a91042906bff17acb38254f7 protects accepted M4a before new mathematics. check_m4_inherited compares every accepted B/W/P result record, stage, ordered binding and type, alongside the existing M2/M3 inheritance guards and accepted module source hashes. This closes the M4a review's next-stage finding.

Independent Git comparisons found all 140 accepted types, mathematical sources (including Boundary/Stationary.lean and Controls.lean), Integrity/KernelAudit, prior scientific contracts/maps, M4 scientific/precision/approval content and toolchain/dependency pins unchanged. The root export adds the new modules. All 153 prior examples remain an exact prefix. The complete full-index Git diff matches the handoff patch. Exactly 16 accepted_type entries are null among 156 comparisons. The distinct accepted-M3 pin is retained. Historical reviewer/worker archives match the preimplementation guard snapshot byte for byte.

All six M4 IDs are populated, with R seven, O three and C six new bindings. Full M4 has 39 bindings and the cumulative library has 156 promises. No M4 result is intentionally deferred. Supporting controls and generated names remain in the owning-module inventory. No new explicit safe axiom, unsafe proof route, custom proof budget or linter suppression was introduced. Accepted M3's scoped budgets are unchanged. Per-root axiom queries skipped on compiler non-roots establish no executable verification claim.

## Composed full-M4 scope and next permitted work

The accepted B/W/P definitions retain direct owner pressure, distinct inviscid-symmetry-traction naming, the positive-density/nonzero-area velocity interpretation, and owner-left/exterior-right original Roe with its two-state spectral hypotheses and sonic equality. The new R/O/C results consume those same definitions and accepted geometry/residual. This establishes the approved stationary boundary-transfer composition, exact balances, transported representation invariance and qualified common-state preservation.

There is no projected tangency update, full symmetry evolution, characteristic/nonreflecting guarantee, entropy/update-positivity repair, time update, mixed-mesh parser or SU2 correspondence. These limits are unchanged from the scientific contract.

After recording separate scoped M4b and full-M4 decisions at this immutable candidate, the next scientific proposal may address M5 time integration. Standing implementation authorization remains active. Preserve all accepted bindings/types/sources, review the next exact scientific scope, address mandatory findings and freeze its contract before implementing it. A repeated implementation-approval request is unnecessary under the recorded standing authorization. This review modifies no repository and initiates no new milestone implementation.

## Declaration locators at the frozen candidate

Assembly declarations below have prefix `CFDLean.Boundary`; controls have prefix `CFDLean.Boundary.AssemblyControls`.

| File | Lines | Declarations |
| --- | --- | --- |
| `CFDLean/Boundary/Assembly.lean` | 11, 48, 162, 166 | `constructedTransfer`, `stationaryResidual`, `meshResidual`, `meshResidual_eq` |
| Same | 52, 57, 70, 77, 84, 171 | `stationary_global_balance`, `stationary_mixed_balance`, `stationary_mass_balance`, `stationary_energy_balance`, `stationary_momentum_balance`, `mesh_global_balance` |
| Same | 37, 96, 176 | `constructed_transfer_reindex`, `stationary_residual_reindex`, `mesh_residual_reindex` |
| Same | 111, 120, 132, 153, 184, 192 | `transfer_compatible`, `stationary_common_defect`, `stationary_common_closed`, `stationary_common_correction`, `mesh_constant_state`, `mesh_common_correction` |
| `CFDLean/Boundary/AssemblyControls.lean` | 92, 136, 224, 188, 242 | `incompatible_wall_residual`, `incompatible_exterior_residual`, `transported_nonzero`, `two_cell_common`, `pressure_force_retained` |

## Trust interpretation

Kernel-checked proof terms establish the stated mathematical propositions within Lean's trusted kernel, its admitted foundational axioms and pinned imported environment. Explicit expected types and immutable baseline/source comparisons additionally detect changes to the accepted statement or its interpretation through definitions. Neither an axiom allowlist nor a successful dependency traversal independently establishes that a scientific specification is appropriate; that requires the statement, hypothesis and definition review above. Source-only reproduction reduces reliance on submitted compiled artifacts while retaining trust in the installed Lean toolchain, build environment and supporting tooling. Executable machine arithmetic and C++ correspondence are outside this decision.

## Completed independent reproduction

The supplied bundle/checkpoint checksum manifests passed. The mathematical candidate and tree were authenticated against the private GitHub repository. From a clean detached clone of the exact candidate, with no .lake directory, the reviewer ran the unchanged scripts/reproduce.sh against that full commit. The installed pinned Lean/Lake 4.19.0 toolchain was reused from the prior independent review. All nine dependency source revisions were fetched afresh with clean tracked sources; both binary-cache controls were active, and the pinned ProofWidgets assets were compiled locally. LEAN_NUM_THREADS was 8.

The reproduction exited 0. The full source build passed, all 16 Python fixtures passed and all 182 Lean examples passed with warnings treated as errors. All 62 protected file checksums passed both before and after the build. Every one of verification.json, kernel-inventory.log, inherited-types.json, bindings-diff.patch and binding-type-diff.json matched the frozen candidate Git blob and the checkpoint worker archive byte for byte. Only evidence/build.log differed among tracked files, as expected from fresh build scheduling.

The regenerated inventory has 1,726 records, 988 safe roots and 21,175 reachable declarations. Its permitted axioms are exactly propext, Classical.choice and Quot.sound; no reachable unsafe declaration was found. The 459 unsafe non-roots comprise 421 definitions and 38 compiler axiom records. All 279 metadata-only records remain visible. These non-roots do not establish an executable verification guarantee.

The separate reviewer-authored checks/Independent.lean also exited 0. It independently traverses types, values, constructors and recursor rules from owning-module safe roots, reproducing the same 988/21,175 counts and axiom set. Its additional kernel-checked compositions connect concrete boundary common-state preservation to positive used-node volume, and isolate the boundary mismatch sum from the actual residual's metric term. Other retained reviewer checks connect the accepted M1 flux to the Roe secant and derivative limit. checks/Arithmetic.py separately reproduces compatible zero and both incompatible residual vectors with exact rational arithmetic and actual standard-tetrahedron edge/patch assembly. This arithmetic is supplementary evidence.

The two acceptance decisions above follow the scientific inspection, source/type preservation checks, complete fresh reproduction and reviewer checks together. They do not derive from the worker's success report. No remote repository was modified.
