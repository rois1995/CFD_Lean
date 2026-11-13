# M3 scientific proposal review

**Subsequent status:** the [independent review](proposal-b0e5d14/Review.md) recommends approval without mandatory amendment, and [Andrea approved implementation](../../specifications/M3-approval.md). The [frozen contract](../../specifications/M3.md) and representation precision govern M3a/M3b. The proposal submission below remains historical; its authorization-pending wording is superseded by that approval record.

Status: proposed, not approved or implemented. The supplied independent M2 review accepts M2d and full M2, but explicitly authorizes no M3 implementation. The next step is independent proposal review followed by Andrea's separate scientific/repository decision.

- [Concrete scientific proposal](../../specifications/M3-proposal.md).
- [Accepted full-M2 decision](../M2/Acceptance.md) and [immutable downstream pin](../../specifications/accepted-M2.json), mathematical revision ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1.
- [Exact preparation program](PreparationChecks.py) and [its output](PreparationChecks.log).

The proposal specifies finite paired incidence, outgoing integrated residuals, boundary ownership, orientation/reindexing invariance, geometric metric defects and conditional constant-state preservation. It then specifies a conforming tetrahedral barycentric median dual and requires derived local/global area closure and determinant-volume identities. Six proposed result IDs cover the abstract assembly and concrete geometry/composition in two independently reviewable stages.

The selected discretization evaluates one original Roe flux on the sum of oriented partial-face vectors with direct nodal states. It does not identify this with the sum of nonlinear Roe fluxes over nonparallel facets. Approval is requested for that aggregation choice and its explicit Euclidean normalization, the tetrahedral restriction, theorem list and audit/preservation plan. Supplied boundary transfers do not select M4 wall/far-field algorithms. There is no second-order accuracy or update-positivity claim.

Blazek's existing approved first edition was inspected at the precise locators recorded in the proposal. Printed pages 142, 143 and 145 were also visually inspected. The ambiguous mean-unit-normal wording and normal-sum equation on page 142 are documented; the proposal requests an explicit project convention rather than asserting an authenticated erratum or silently assuming unit length. No new source or edition is introduced.

The preparation program uses only Python's standard library and exact Fraction arithmetic. It checks all 24 subdivision volumes and four local dual closures on both the standard and an oblique tetrahedron, outward triangle pairing, shared-face patch cancellation and all five dual closures on a two-tetrahedron mesh, positive/total volumes, a three-node residual cycle and orientation/reindexing, and examples of excluded degenerate/three-fold-face inputs. These are small design controls, not a general mesh validator, Lean proofs or M3 implementation. Re-run with `python3 reviews/M3/PreparationChecks.py`.

No accepted Lean source, toolchain, dependency pin, frozen specification, result binding, checker or submitted deterministic audit output is changed by this closeout/proposal. All 27 supplied independent-review payload hashes and their original manifest were checked; the five independent deterministic outputs equal the accepted candidate's Git blobs. The nine existing checker fixtures still pass. No new cold build is needed or claimed for documentation and proposal work; the independent cold replay is preserved unchanged.

The source SHA256 manifest is refreshed for current documentation, the downstream pin and proposal. The machine evidence and historical worker replay continue to describe the accepted mathematical candidate. Before implementing M3, extend inherited guards to all 66 accepted M2 bindings/types and keep every accepted mathematical source fixed. This is part of the proposed implementation plan, not an already performed audit-tool change.

See Reviewer_Prompt.md for the ready-to-send independent proposal review request.
