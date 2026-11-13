# CFD_Lean

Independent exact-real Lean 4 contracts for compressible CFD. M1 specifies ideal-gas Euler states, conditional primitive/conservative conversion identities, admissibility and physical flux for oriented area vectors in arbitrary finite dimension. See [the contract](specifications/M1.md), [source/proof map](references/M1.md) and [approval record](specifications/M0-approval.md).

The library imports mathlib only. A future SU2 verification package may depend on an immutable CFD_Lean revision, using separate working trees and build directories.

## Reproduce the independently reviewed M1 candidate

Frozen mathematical candidate: `0a88e36b3810cd5adc3881db526ca8a35f81afbb`.

Use a fresh, clean, detached checkout of that commit with no `.lake`. Put Lean/Lake 4.19.0, Git, Python 3, Node, npm, sha256sum and realpath on PATH. Keep a separate copy of [the published review bundle](reviews/M1/) outside the fresh checkout. Its scripts and logs are preserved byte-for-byte from the submitted reviewer evidence, with their original SHA256SUMS.

From the fresh candidate checkout, replace `/absolute/path/to/published-review` below with that separate `reviews/M1` directory, and choose log directories outside the checkout:

```bash
git checkout --detach 0a88e36b3810cd5adc3881db526ca8a35f81afbb
sha256sum -c evidence/SHA256SUMS
bash /absolute/path/to/published-review/reviewer/ReproduceM1.sh ../M1-replay-logs
bash /absolute/path/to/published-review/reviewer/RunReviewerChecks.sh ../M1-independent-checks
```

The tested reproduction script checks the frozen snapshot, fetches all nine manifest-pinned source trees, disables both binary-cache mechanisms (`LAKE_NO_CACHE=1` and `MATHLIB_NO_CACHE_ON_UPDATE=1`), builds pinned ProofWidgets JavaScript locally using its npm lockfile, and runs the original verifier. The widget bootstrap is necessary: the pinned mathlib blocks a missing widget asset build during the normal downstream build. Setting only the mathlib update-hook variable is insufficient for a fresh source-only reproduction.

Check the committed hashes **before** verification: the verifier regenerates evidence/SHA256SUMS. The frozen Git commit remains the baseline. The reviewer independently completed and replayed the source-only procedure; detailed commands and results are in [the report](reviews/M1/CFD_Lean_M1_Independent_Review.md).

## Development verification

Lean: `leanprover/lean4:v4.19.0`. Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Transitive dependencies are pinned in lake-manifest.json.

After the pinned dependency sources and widget assets have been bootstrapped, run:

```bash
sha256sum -c evidence/SHA256SUMS
LAKE_NO_CACHE=1 MATHLIB_NO_CACHE_ON_UPDATE=1 python3 scripts/verify.py
```

This incremental command is not the complete fresh-checkout bootstrap; use the source-only procedure above for the frozen M1 candidate. Project proof terms are checked by Lean's kernel. The current verifier inventories elaborated project modules, retains qualified declaration names, rejects duplicate rows, checks cumulative approved result bindings and their frozen contract hash, and protects accepted M1 source hashes. It reports all logical roots and compiler metadata separately. Run the parser/coverage fixtures with `python3 -m unittest discover -s scripts -p test_verify.py`. Historical M1 review scripts remain tied to the original frozen M1 revision.

## Review status

The independent decision is **Accept M1**, with both original review conditions closed. The accepted mathematical revision is `0a88e36b3810cd5adc3881db526ca8a35f81afbb`; documentation follow-up `180ff1be1aa95d943574efd9c05cd4de320a88b6` closed the conditions. See the supplied [final acceptance record](reviews/M1/CFD_Lean_M1_Acceptance.md). The original conditional report and evidence remain intact as review history.

Acceptance covers the exact-real M1 state algebra and oriented physical flux only. The [next-step handoff](reviews/M1/START_HERE_Agent_A.md) requests an original 3D Roe-flux proposal. The [M2 proposal](specifications/M2-proposal.md) received an independent recommendation for implementation. Andrea approved M2 and authorized M2a on 2026-11-13; see [the approval record](specifications/M2-approval.md), [frozen contract](specifications/M2.md), and [result bindings](specifications/M2-results.json). M2a (M2-J) is independently accepted without outstanding conditions at `3788009de306d80e002976e66ba2b1103e2dbd83`; see [the acceptance record](reviews/M2a/Acceptance.md). The original worker checkpoint remains identifiable at `4d845ad`. The M2b (M2-A/R/L) implementation candidate now passes local kernel, expected-type and dependency checks; independent M2b acceptance and acceptance of the complete M2 Roe flux remain pending. The current checker compares inherited bindings and types with the immutable accepted M2a revision and elaborates explicit expected-type checks. The replay script compares regenerated audit evidence with the candidate byte for byte.

The approved private remote is [rois1995/CFD_Lean](https://github.com/rois1995/CFD_Lean). Later milestones are Roe flux, node-centered assembly, selected boundary algorithms and explicit time update. Books and papers remain in the external reference collection; repository reference records contain metadata and source locators only.

## Accepted M2a checkpoint

See [M2a source/result traceability](references/M2a.md). This implements M2-J: coordinate round trips, the explicit physical Jacobian action, the Frechet derivative of the actual M1 flux for fixed arbitrary normal/area and nonzero density, admissible-domain openness, Euclidean area normalization and zero-area derivative. The M2b extension below proves the subsequent two-state obligations using this accepted baseline.

A fresh source-only replay for a new frozen checkpoint uses `bash scripts/reproduce.sh FULL_COMMIT_SHA /outside/checkout/logs` from a clean detached checkout of that exact full commit, without `.lake`. The script reuses the reviewed pinned-source and widget bootstrap, disables both binary-cache mechanisms and then runs the current audit and fixtures. It is separate from the historical M1-specific replay script.

## M2b implementation candidate

See [M2b source/result traceability](references/M2b.md). M2-A proves square-root weight bounds, symmetry, the enthalpy variance identity and positive averaged sound speed. M2-R proves parameter-map recovery of the actual M1 state and flux, their Frechet derivatives B/C, exact midpoint jumps, a two-sided inverse of B, the C B-inverse matrix order and the arbitrary-normal/integrated secant identity. M2-L proves joint operator-norm continuity, diagonal equality with M2a's physical Jacobian and the full equal-state limit. These results use the unchanged approved contract and accepted mathematical sources.

The result map contains 37 active J/A/R/L theorem bindings, including all eight unchanged accepted J types. `StatementChecks.lean` provides explicit inherited/new expected-type checks and exact stationary-contact/shear sound-speed examples. The generated `evidence/bindings-diff.patch` and `evidence/binding-type-diff.json` expose the full binding/type changes from accepted M2a. Fresh source replay is required before requesting independent acceptance of the frozen combined candidate; its evidence is recorded separately. M2c/M2d remain deferred.
