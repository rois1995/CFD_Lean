# M2a provenance and acceptance map

Status: independently accepted at `3788009de306d80e002976e66ba2b1103e2dbd83`; see reviews/M2a/Acceptance.md. The remaining description records the original implementation scope. The approved mathematics is frozen in specifications/M2.md and bound by its SHA-256 in specifications/M2-results.json. The approved result ID is M2-J; M2-A/R/L remain subsequent M2b obligations.

## Sources and project derivations

- M1's accepted Conservative/Primitive state, pressure and physicalFlux definitions remain byte-identical to mathematical candidate 0a88e36. The verifier checks their source hashes, including the original Integrity.lean checks.
- Blazek, first edition 2001: p. 12 Eq. (2.12), p. 16 Eqs. (2.20)–(2.22), p. 18 Eq. (2.29); Appendix A.7 p. 419 Eqs. (A.44)–(A.47). These give the state, energy/enthalpy convention, actual normal physical flux, ideal-gas pressure and physical Jacobian. Moving-grid terms are excluded by the stationary-grid choice.
- Toro, third edition 2009: p. 354 Eqs. (11.47)–(11.53) provide an x-direction cross-check. No Roe matrix, averages or entropy correction is implemented in M2a.
- The 5-coordinate chart, arbitrary fixed-normal linear action, explicit Euclidean face geometry and Frechet derivative proofs are project derivations from the accepted M1 definitions, not equations asserted merely by source naming.

## Definitions and result bindings

Coordinates.encode/decode give the chart (rho,mx,my,mz,energy density) and its inverse. The standard finite-function norm supports calculus topology only. Coordinates.area is explicitly sqrt(squareSum S); unitNormal uses this Euclidean length. A nonzero face is proved to give a unit vector and to reconstruct S by area times normal. The oblique (2,3,0) check requires sqrt(13), not the default supremum norm 3.

PhysicalJacobian.coordinateFlux is exactly encode (physicalFlux gamma (decode x) S), so the derivative is of M1's actual flux. The explicit jacobian is a continuous linear map, built from component projections and the proposed pressure/normal increments. jacobian_action relates this representation to the record-field formula in the approved contract.

The derivative proofs require x[0] != 0, with fixed arbitrary real gamma and fixed arbitrary vector n. No unit-normal, admissibility, sound-speed or Roe linearization conclusion is assumed. The physical domain additionally carries gamma > 1 and M1 admissibility. Openness is proved in chart coordinates. Integrated scaling requires nonzero S and uses the Euclidean area; the zero-area derivative is zero without a density hypothesis.

specifications/M2-results.json binds the full qualified M2-J theorem names before acceptance. Other declarations are audited supporting mathematics. There is no claim that implementing M2a completes M2b's equal-state Roe identification or any Roe flux theorem.

## Audit and evidence

KernelAudit.lean inventories the imported project modules by owning module, including every safe logical declaration and generated theorem. Compiler metadata names without a checked-kernel constant are reported as metadata-only entries; no mathematical root is inferred from those names. The dependency traversal still fails if a mathematical root references a missing constant. Unsafe executable auxiliaries are reported explicitly and are not treated as mathematical roots; the full dependency traversal fails if any is reachable from a mathematical root. Non-unsafe project axioms fail immediately. The only permitted axiom leaves are propext, Classical.choice and Quot.sound.

The Python parser retains full qualified names and rejects any duplicate record, including identical duplicates. Module coverage is compared with all project mathematical source modules. The current promised result list is checked for actual theorem declarations, and the other approved milestone IDs are reported as deferred. The frozen contract hash and accepted M1 source hashes are validated before build. Parser/foundation/missing-result fixtures are exercised by scripts/test_verify.py.

The original candidate has now passed independent review of the theorem types, domain assumptions, generated auxiliaries, checker and full proof dependency evidence. Later stages still require their own independent acceptance.
