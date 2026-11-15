# M3a source, result and assumption map

Worker implementation of the approved M3a I/R/O and conditional C obligations. Andrea approved the reviewed plan after the independent proposal recommendation; see specifications/M3-approval.md. The reviewed proposal is frozen byte-for-byte as specifications/M3.md, with its approved representation precision in M3-representation.md at 3189a603b3f6af953f0828d6b2e239320fd2cd20. M3a is independently accepted at a70270c3f771e66bcaaebc18b8480c32f9606b1e; see reviews/M3a/Acceptance.md. This historical stage map retains its original counts. The subsequent concrete extension and independently accepted full-M3 verdict are recorded in M3b.md and reviews/M3/Acceptance.md.

## Assembly and accepted physical interface

CFDLean/Discretization/Assembly.lean adds one module. Interfaces stores tail/head maps with a distinct-endpoint proof and a separate owner map for exterior pieces. It is abstract incidence data, not a mesh importer or a proof of mesh validity. Residuals are finite sums of incidence-weighted edge transfers and one-owner boundary transfers. They use the accepted finite real coordinate vectors. The dimension parameter permits the same assembly on the required three-component area vectors and five-component conserved transfers; no additive physical-state instance is introduced.

incidence is the tail indicator minus the head indicator. Tail/head, exact support and finite-sum statements prove the unique positive and negative contributions, and residual_outgoing identifies this assembly with explicit filtered outgoing/incoming enumeration. Global balance follows by finite sum exchange, first for arbitrary transfers and then for the concrete accepted Roe transfer. Neither geometric closure, positivity of volumes nor a desired cancellation conclusion is an assumption of global_balance.

roeTransfer is exactly encode(numericalFlux gamma U_tail U_head S_e), with no second area factor, alternate solver, reconstruction or boundary algorithm. outwardTransfer evaluates the head's own outward orientation independently, swapping states and negating area. Its equality with incidence times the stored edge transfer uses accepted M2 reversal. This separates algebraic scatter cancellation from the physical interface-reversal identity. Zero-area transfer follows from the accepted explicit M2 zero branch.

Reversing any selected interfaces swaps endpoints, reverses their areas and negates their transfers. Incidence signs reverse too, leaving each node residual unchanged. Reindexing transports nodes, edges and exterior-piece IDs together through equivalences, including endpoint maps, boundary ownership, nodal states, area vectors and supplied boundary transfers. It is not merely edge-loop permutation.

physicalTransfer views the actual M1 integrated physical flux as a linear map of area, proved using the accepted physicalFlux_add and physicalFlux_mul theorems and the accepted coordinate layout. The same finite assembly commutes with this linear map. At a common nodal state, accepted M2 consistency identifies each edge transfer with physicalTransfer, while boundary data are explicitly required to be physicalTransfer on their own areas. The result is the actual physical flux on metricDefect. A zero defect gives zero residual.

These algebraic identities have raw-state types stronger than their physical specializations; they assign no physical meaning to invalid states. Physical use retains common gamma>1 and M1 admissibility. The constant-state result requires compatible boundary transfers in its statement. It does not prove that arbitrary wall/far-field algorithms preserve an arbitrary constant state.

## Qualified declaration map

All following names have prefix CFDLean.Assembly. specifications/M3-results.json is the machine-readable map. The six approved IDs remain unchanged; C has separate conditional M3a and concrete M3b parts, so an empty future part cannot masquerade as complete M3 acceptance.

| Approved ID/part | New declarations | Scope |
| --- | --- | --- |
| M3-I / M3a | incidence_tail, incidence_head, incidence_other, incidence_eq_one, incidence_eq_neg_one, incidence_sum, incidence_smul, residual_outgoing | Distinct endpoints, paired signs/support and explicit outgoing enumeration. |
| M3-R / M3a | global_balance, roe_global_balance | Sum of node residuals equals sum of supplied exterior transfers; includes actual Roe assembly. |
| M3-O / M3a | outwardTransfer_eq, residual_reverse, roe_residual_reverse, residual_reindex, roe_residual_reindex, roeTransfer_zero | Actual outward physical orientation, reversal and transported relabeling, including zero area. |
| M3-C / M3a | constant_state_residual, constant_state_closed | Compatible constant-state flux equals physical flux on metric defect; closure implies zero residual conditionally. |
| M3-G, M3-V and M3-C / M3b | No declarations claimed | Tetrahedral median-dual construction, derived geometric closure, determinant volumes and concrete composition remain later work in the approved sequence. |

There are 18 new promised M3a bindings and 66 accepted inherited M2 bindings, for 84 cumulative promises. Supporting definitions, lemmas, structure-generated declarations and compiler auxiliaries remain visible in the owning-module audit. No M3-G/V conclusion or concrete M3-C instance is hidden in this stage.

## Traceability, controls and audit

The approved Blazek first-edition source locators and explicit area-vector convention remain those in M3.md. Abstract finite-sum/transport proofs here are project derivations of that approved residual and edge-pairing contract, consuming the actual accepted M1/M2 definitions. No new source, variant, entropy correction or SU2 dependency is introduced. Concrete aggregation of triangular vectors belongs to M3b; this stage accepts the oriented edge vectors as input.

StatementChecks.lean retains all 56 inherited examples and adds 17 M3a examples (73 total). Exact controls include the signed five-component residual of a single interface, a nontrivial three-node cycle with independently specified node residuals, a nonempty admissible rest state on a closed two-node metric example, actual accepted Roe flux with compatible and incompatible boundary data, and simultaneous node/exterior relabeling moving the nonzero residual to the corresponding node. Generic expected-type checks cover finite boundary balance, physical outward orientation, arbitrary selected reversals, all transported reindexings, explicit outgoing enumeration and conditional constant-state preservation. Geometry in the two-node test is supplied abstract data, not a tetrahedral construction.

The inherited guard is pinned to accepted full M2 ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1. All 66 ordered bindings/stages/types and accepted mathematical sources are protected. The 11 checker fixtures cover all 12 inherited result groups, forbidden/unsafe and duplicate audit records, missing bindings, frozen M3 contract metadata and part layouts, and the separation of conditional versus deferred concrete C. Frozen M3 contracts and metadata are checked against immutable approval before building. The current machine evidence records M2 acceptance separately from M3a's pending independent verdict.

A mathematical checkpoint also requires the unchanged fresh pinned-source replay procedure, both binary-cache controls and exact comparison of all five deterministic audit outputs. Worker checks and replay are not independent scientific acceptance. M3b's G/V and concrete C, M4 boundary algorithms, time stepping, entropy/update-positivity properties and SU2 correspondence are not claimed here.
