# M2a implementation checkpoint

Worker checkpoint, 2026-11-13. Independent mathematical acceptance is pending. This is the M2a portion of the approved plan; the combined M2a/M2b checkpoint is not yet complete.

- Immutable mathematical candidate: [`3788009de306d80e002976e66ba2b1103e2dbd83`](https://github.com/rois1995/CFD_Lean/commit/3788009de306d80e002976e66ba2b1103e2dbd83).
- Approval and frozen contract: `79fd2a03d7b15325c56a88ec83991b4fb4f498bb`; [approval record](../../specifications/M2-approval.md), [contract](../../specifications/M2.md), [qualified result bindings](../../specifications/M2-results.json).
- Provenance and proof scope: [M2a source map](../../references/M2a.md).

## Implemented M2-J bindings

All names below are actual elaborated theorem declarations. Their complete types, project dependencies and transitive axiom lists are in [verification.json](../../evidence/M2a-source-replay/verification.json).

| Qualified declaration | Result and hypotheses |
| --- | --- |
| `CFDLean.Coordinates.decode_encode` | Conservative records survive encoding and decoding. |
| `CFDLean.Coordinates.encode_decode` | Every five-coordinate vector survives decoding and encoding. |
| `CFDLean.PhysicalJacobian.hasFDerivAt_coordinateFlux` | The displayed continuous linear map is the Frechet derivative of `encode (physicalFlux gamma (decode x) n)`, for fixed arbitrary gamma and n, assuming only nonzero density. |
| `CFDLean.PhysicalJacobian.isOpen_admissible` | The fixed-gamma admissible domain is open in chart coordinates. |
| `CFDLean.Coordinates.unitNormal_dot_self` | A nonzero face vector normalized by its Euclidean area has dot product one with itself. |
| `CFDLean.PhysicalJacobian.hasFDerivAt_integratedFlux` | The actual area-vector flux derivative is area times the unit-normal Jacobian; density and face vector are nonzero. |
| `CFDLean.PhysicalJacobian.jacobian_action` | The coordinate linear map has precisely the record-field action in the frozen contract. |
| `CFDLean.PhysicalJacobian.hasFDerivAt_zeroArea` | The zero-area flux derivative is zero at every coordinate state, including zero density. |

The derivative theorem does not assume admissibility, a unit normal or a derivative conclusion. The physical interpretation uses gamma > 1 and the accepted admissibility predicate. Euclidean area is explicitly `sqrt(squareSum S)`; the finite-function norm is used only for calculus topology. The supporting theorem `CFDLean.Coordinates.area_oblique` proves that the area of (2,3,0) is sqrt(13).

## Verification and audit

The successful local build and upgraded audit inventory 167 qualified records. Their 118 safe mathematical roots reach 13,897 declarations, with only `propext`, `Classical.choice` and `Quot.sound` as axiom leaves and no reachable unsafe declaration. The 35 unsafe executable/compiler records and 14 metadata-only names remain visible as non-roots. All eight M2-J bindings and all nine pinned dependency revisions pass. The eight parser/foundation/coverage fixtures pass.

`KernelAudit.lean` uses elaborated owning modules, includes generated logical declarations, rejects non-unsafe project axioms and traverses the complete mathematical-root dependency closure. The Python checker preserves qualified names, rejects duplicate records, checks cumulative stage obligations and protects the approved contract hash and accepted M1 source hashes. The checker is part of the review scope.

The accepted M1 State, PhysicalFlux and Integrity sources are byte-identical to their accepted mathematical candidate. The Lean/mathlib/dependency pins are unchanged. Original M1 and M2 proposal-review evidence remains historical and unmodified.

The fresh pinned-source replay of the exact candidate **passed**, starting from a clean detached checkout without `.lake`. All nine dependency source trees were fetched at their manifest revisions. Both Lean binary-cache mechanisms were disabled, and the pinned widget assets were built locally. The complete build, eight fixtures, elaborated audit, dependency checks and pre/postbuild source checksums passed. The fresh verification JSON equals the candidate's local evidence; only `evidence/build.log` changed during replay.

The [archived replay logs](../../evidence/M2a-source-replay/), [replay record](../../evidence/M2a-source-replay/replay.json) and their [checksums](../../evidence/M2a-source-replay/SHA256SUMS) are implementation-worker evidence. This was not an independent reviewer run.

To reproduce, put Lean/Lake 4.19.0, Git, Python 3, Node/npm, realpath and sha256sum on PATH. From a fresh clean checkout without `.lake`:

```bash
git checkout --detach 3788009de306d80e002976e66ba2b1103e2dbd83
bash scripts/reproduce.sh 3788009de306d80e002976e66ba2b1103e2dbd83 /outside/checkout/M2a-replay-logs
```

The script verifies the committed hashes before regenerating evidence and refuses a different or dirty candidate checkout. Check archived log hashes from `evidence/M2a-source-replay` with `sha256sum -c SHA256SUMS`.

## Unresolved work and next step

- M2b: **M2-A, M2-R, M2-L**. Roe averages and sound-speed positivity; parameter-map endpoint recovery, midpoint identities, invertibility and A B = C; secant identity and equal-state physical-Jacobian identification/limit. No declarations are claimed for these IDs.
- M2c: **M2-E, M2-D, M2-O**, including complete eigenstructure, projectors and orientation results.
- M2d: **M2-F1, M2-F2, M2-F3, M2-F4, M2-C**, including the final numerical flux and counterexample.

There are no sorry/admit placeholders for these goals. They are explicitly deferred in the result bindings and machine evidence. No Roe flux, positivity-preserving method, mesh assembly, floating-point implementation or SU2 correspondence is claimed.

Next implementation work is M2b under the approved plan. The combined M2a/M2b checkpoint must provide qualified J/A/R/L declarations and updated proof evidence before the later stages. An independent reviewer supplies scientific acceptance; this worker checkpoint and its replay cannot supply that decision.
