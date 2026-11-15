# M4b and composed full-M4 source/result map

M4b implements the already approved R/O/C stage on independently accepted M4a 37c1e6ee4618b0183135c2795b3aa6ebea2f22d5. The supplied M4a verdict accepts B/W/P without conditions; its 25 original payloads and five exact candidate/checkpoint matches were verified and preserved under reviews/M4a/independent-37c1e6e. See reviews/M4a/Acceptance.md and specifications/accepted-M4a.json. The original M4 contract, naming/domain precision and approval freeze remain 0cff4af244b85f4e2071e7bf941d40fdd0a399b5. The user approved the two-stage plan and subsequently gave standing implementation authorization in reviews/Standing_Authorization.md; no repeated approval is needed.

Before M4b mathematics, commit 4c0a4d5 extended the inherited guard to all 140 accepted bindings/types, exact B/W/P records/stages and all mathematical sources, including Boundary/Stationary.lean and Boundary/Controls.lean. Sixteen checker fixtures and full baseline verification passed. The M3 acceptance metadata retains its distinct e2ea538 mathematical pin when the current inherited baseline advances to accepted M4a. Original archives and historical pending fields remain unchanged.

## Actual selected-rule residual and component balance

Boundary/Assembly.lean defines constructedTransfer from the actual accepted transfer, owner state, boundary kind, prescribed exterior value and outward integrated area. stationaryResidual passes this exact g to the unchanged Assembly.residual with the unchanged accepted interior roeTransfer. No arbitrary transfer is substituted for the algorithm. meshResidual derives kinds and exterior values from the accepted primal-face maps and uses the exact accepted MeshData interfaces, edgeArea and boundaryArea. meshResidual_eq identifies it with the identical accepted patchTransfer. No geometry, normal, ownership, Roe definition, extra area factor, volume division or time step is introduced.

stationary_global_balance derives the complete five-vector boundary sum from accepted M3 finite incidence. stationary_mixed_balance separates the prescribed-exterior Roe sum and pressure-traction sum. Mass/energy balances contain only prescribed-exterior contributions. Momentum contains the actual owner's pressure times T for wall and inviscid-symmetry traction pieces, in addition to prescribed contributions. These finite algebraic identities have stronger raw-state types; physical use retains common gamma>1 and admissible used-node states, with exterior admissibility on prescribed faces. No general zero total momentum or zero residual is asserted.

## Fully transported data

constructed_transfer_reindex derives pointwise transport from transported kinds, prescribed states, nodal states, ownership and areas under node/edge/boundary equivalences. stationary_residual_reindex then invokes the accepted M3 Roe transport theorem on this constructed g. mesh_residual_reindex first derives actual patch kinds/data from face maps, then transports their values and all actual interface areas/records. It is not merely edge-loop order, and it assumes no supplied equality certificate for g. Rebuilding a separately renumbered geometric mesh and proving constructor naturality remains outside the approved contract.

## Qualified concrete common-state result

transfer_compatible proves the actual selected transfer equals physicalTransfer under zero normal momentum for both traction kinds or matching prescribed exterior state. It uses the protected M4a wall iff and actual Roe consistency. stationary_common_defect derives the residual as physicalFlux on the actual metric defect. stationary_common_closed is its explicitly conditional generic consequence.

The public mesh_constant_state retains gamma>1, actual M1 admissibility, M.Conforming, per-patch traction tangency and prescribed-data matching. It supplies the metric zero from accepted M.metric_closed, not an input closure certificate. The same concrete interfaces/areas and selected patchTransfer are used throughout. Generic helper algebra is stronger than the physical type; no physical interpretation of invalid inputs is added. Matching prescribed data are sufficient, not necessary in every spectral regime. No velocity projection, evolved tangency, full symmetry solution, characteristic/nonreflecting result, update positivity or entropy claim follows.

residual_boundary_difference and stationary_common_correction are exact subtraction identities for the same accepted residual and constructed transfer. mesh_common_correction inserts derived closure to express the actual common-state residual as the sum of selected-boundary minus physical-boundary transfers. These support explicit incompatible controls. They do not insert a correction into the numerical algorithm or replace it with an arbitrary transfer cycle.

## Controls on accepted geometry and actual algorithms

Boundary/AssemblyControls.lean uses the same accepted standard, genuinely oblique and conforming two-cell data. The standard mixed wall/open case preserves every admissible moving(q,1) common state tangent to its wall. An all-wall standard rest state and an all-inviscid-symmetry-traction oblique rest state preserve the state for arbitrary unused exterior values.

For the two positively ordered cells [0,1,2,3] and [0,2,1,4], two exterior y=0 faces are assigned slip-wall and inviscid-symmetry traction; other exterior faces use prescribed-exterior Roe. One actual owner has all three kinds on distinct actual faces. A moving(q,1) common state is tangent to both traction faces, and every concrete residual is zero. The accepted positive nodal volumes and total 1/3 remain available and are explicitly checked; no time update is defined. All-wall global mass/energy balance is also checked on this actual geometry for arbitrary nodal states, with a nonconstant admissible pressure family as a physical example.

The actual wall-incompatible control uses rho=1, momentum=(0,0,1), energy=3/2 at gamma=2 (pressure 1). Exterior data match this common state, but the z=0 wall tangency condition fails. The actual owner-0 residual is (1/6,0,0,1/6,5/12), hence nonzero.

The actual exterior-incompatible control uses the admissible resting pressure-1 common state and pressure-3 prescribed data on just one open primal face, with matching data on other open faces and a compatible rest wall. The accepted polynomial projectors/normal-reversal/area laws give the actual numericalFlux on its negative-axis owner patch. The owner-0 residual is (-1/12,-1/6,0,0,-1/3), hence nonzero. Face maps assign that exterior value coherently to every owner of the face. The single-face bookkeeping proof establishes that every other actual transfer is physical; no arbitrary residual correction is assumed or supplied.

A nontrivial simultaneous swap of nodes, two actual edge IDs and wall/open boundary records transports the kinds and the nonconstant exterior data as well as the owner states and areas. The nonzero residual moves to node 1 with the same vector. An explicitly abstract finite-interface balance control has total transfer (0,1,0,0,0), demonstrating retained pressure momentum while mass/energy vanish; no geometric closure is claimed for that abstract interface.

## Promised obligations and preservation

All following declarations have prefix CFDLean.Boundary. The unchanged six-ID/stage layout is in specifications/M4-results.json.

| ID/stage | New bindings | Scope |
| --- | --- | --- |
| M4-R / M4b | stationary_global_balance, stationary_mixed_balance, stationary_mass_balance, stationary_energy_balance, stationary_momentum_balance, meshResidual_eq, mesh_global_balance | Actual-rule vector/component balance and exact concrete residual. |
| M4-O / M4b | constructed_transfer_reindex, stationary_residual_reindex, mesh_residual_reindex | Fully transported constructed transfers and actual generic/concrete residual. |
| M4-C / M4b | transfer_compatible, stationary_common_defect, stationary_common_closed, stationary_common_correction, mesh_constant_state, mesh_common_correction | Local-to-concrete qualified compatibility, derived closure and exact mismatch identities. |

There are 16 new bindings (seven R, three O, six C), for 156 cumulative promises. All 140 accepted bindings/types and source files are unchanged; the import-only umbrella adds the new export and the 153 accepted examples remain an exact prefix. All six M4 IDs are populated and no M4 result is deferred. Supporting lemmas, numeric controls and compiler-generated names remain included in owning-module/transitive audits. Frozen scientific/precision/approval content, result metadata/stages and all compiler/dependency pins remain fixed.

The source is the same approved Blazek first edition and exact locators in frozen M4.md, together with accepted M1 pressure/physical flux, M2 original Roe and M3 geometry/incidence plus accepted M4a transfer definitions. The finite sum/projection, relabeling, compatibility and explicit-control proofs are project derivations. No new literature, publisher correction or SU2 source is introduced.

Submitted M4b requires the complete fresh pinned-source replay with both binary caches disabled, nine fresh pins, local pinned widget compilation, source checksum preservation and five exact deterministic output comparisons. Worker checks/replay are not independent scientific acceptance. Both scoped M4b R/O/C and composed full M4 are independently accepted without conditions at 3a586a42546cba1784cc79269e3f9d1c5d843f0c; see reviews/M4b/Acceptance.md and reviews/M4/Acceptance.md.
