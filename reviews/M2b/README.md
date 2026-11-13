# Combined M2a/M2b review checkpoint

Worker submission, 2026-11-13. M2a is independently accepted; M2b is awaiting independent scientific review. This checkpoint does not implement M2c/M2d or the complete Roe numerical flux.

- Immutable combined mathematical candidate: [`c92c0f66360f85c0a3339ab9b30fc00c39ee5f93`](https://github.com/rois1995/CFD_Lean/commit/c92c0f66360f85c0a3339ab9b30fc00c39ee5f93).
- Accepted M2a baseline: `3788009de306d80e002976e66ba2b1103e2dbd83`; [acceptance and original reviewer evidence](../M2a/Acceptance.md).
- Frozen approved scientific contract: [M2.md](../../specifications/M2.md), unchanged from `79fd2a03d7b15325c56a88ec83991b4fb4f498bb`.
- [Qualified declaration map](../../specifications/M2-results.json), [source/proof traceability](../../references/M2b.md), [explicit expected-type checks](../../StatementChecks.lean).

## Delivered obligations

| ID | Qualified theorem bindings | Scope |
| --- | --- | --- |
| M2-J | 8 inherited | Accepted coordinate chart, actual M1 physical derivative, Euclidean face geometry and zero-area case. Bindings and types are unchanged. |
| M2-A | 10 new | Positive square-root weights, sum one and strict upper bounds, state symmetry, the exact enthalpy variance identity, positive averaged sound-speed square and speed. |
| M2-R | 15 new | Actual endpoint state/flux recovery; Frechet derivatives B/C; exact quadratic midpoint jumps; positive midpoint density parameter; explicit two-sided inverse and bijectivity of B; A B = C, A = C B-inverse, arbitrary-direction and integrated secant identities. |
| M2-L | 4 new | Joint operator-norm continuity on admissible state pairs, equal-state equality with M2a's physical Jacobian, the actual derivative at equal states, and the full two-state equal-state limit. |

The parameter and secant proofs use the actual M1 flux. They do not assume the desired secant identity or any spectral conclusion. The approved C B-inverse order is proved without inverting C, so zero characteristic speeds are not excluded. No independently selected averaged density is introduced.

Physical results use the approved common gamma > 1 and M1-admissible endpoints. Some supporting results hold on the larger positive-density domain or for arbitrary fixed directions. The exact hypotheses and conclusions are retained in the generated types. Integrated scaling uses the accepted Euclidean area; the general raw-direction secant includes zero area without normalization. The continuity theorem is in the normed space of continuous linear operators, not only pointwise continuity of matrix actions. The equal-state derivative and limit explicitly use the accepted M2a Jacobian.

## Review findings addressed

The original M2a review has no outstanding acceptance condition. Its two nonblocking audit limitations are addressed for this submission:

1. The checker reads bindings/types and mathematical source hashes from the immutable accepted M2a Git object. It fails if an inherited binding, stage, theorem type or accepted definition/proof source changes. The import-only CFDLean.lean umbrella is explicitly allowed to export the new module; it introduces no mathematical definitions. The approved contract is also compared with its immutable approval revision. A regression fixture rejects substitution of a different existing theorem and a weakened inherited type. New M2b types still require scientific review.
2. The replay compares regenerated verification JSON, kernel inventory and binding/type comparison outputs with the exact candidate byte for byte. A different cold-build transcript is expected and retained separately.

The [literal Git diff of bindings and audit types](bindings-and-types.patch) compares the two immutable revisions without omitted hunks. The [full binding-file Git diff](../../evidence/bindings-diff.patch) and [complete accepted/current type comparison](../../evidence/binding-type-diff.json) expose every active binding/type change. A null accepted type identifies a new M2b claim, not an accepted result. [inherited-types.json](../../evidence/inherited-types.json) records the eight unchanged J types. StatementChecks.lean elaborates 22 examples: the eight inherited interfaces, twelve M2b interface checks, and two exact stationary-contact/shear sound-speed examples. The derivative and endpoint/secant checks name the M1 flux directly.

## Verification

The local build, all 37 bindings, all 22 expected-type/examples checks, nine Python fixtures and all nine dependency revisions pass. The kernel inventory has 261 qualified records and 212 safe mathematical roots, reaching 14,536 declarations. The only axiom leaves are propext, Classical.choice and Quot.sound; no unsafe declaration is reachable. The 35 unsafe compiler/executable records and 14 metadata-only names remain explicitly visible as non-roots.

M1 and accepted M2a definition/proof files are byte-identical to their accepted revisions. The import-only umbrella now exports Roe.Linearization, which transitively imports the accepted core. The toolchain, Lake configuration, dependency pins, M1 specification and approved M2 contract are unchanged. The original worker M2a submission and independent review are retained unmodified as historical evidence.

The fresh pinned-source replay of the exact candidate **passed** from a clean detached checkout without `.lake`. All dependency sources were fetched at their manifest revisions, both binary-cache mechanisms were disabled, and the pinned widget assets were built locally. All 28 source checksums passed before and after the build. The full build, nine fixtures, 22 Lean interface/examples checks, 37 theorem bindings, eight inherited types and nine dependency pins passed. Only `evidence/build.log` changed.

The [comparison log](../../evidence/M2b-source-replay/audit-comparison.log) records byte-for-byte agreement with all five original candidate audit/binding/type outputs. The [complete replay evidence](../../evidence/M2b-source-replay/), [replay record](../../evidence/M2b-source-replay/replay.json) and [log checksums](../../evidence/M2b-source-replay/SHA256SUMS) preserve the results. This was a worker reproduction, not an independent reviewer run.

To reproduce, put Lean/Lake 4.19.0, Git, Python 3, Node/npm, sha256sum and realpath on PATH. Use a fresh clean checkout without `.lake` and an external log directory:

```bash
git checkout --detach c92c0f66360f85c0a3339ab9b30fc00c39ee5f93
bash scripts/reproduce.sh c92c0f66360f85c0a3339ab9b30fc00c39ee5f93 /outside/checkout/M2b-replay-logs
```

The history must include the immutable accepted/approved revisions used by the checker; a normal full clone does. The script refuses the wrong or dirty candidate, validates the original source hashes before regenerating evidence, and asserts exact audit comparisons. Check archived log hashes from `evidence/M2b-source-replay` with `sha256sum -c SHA256SUMS`.

## Reviewer request and unresolved work

Please independently assess M2-A/R/L and preservation of accepted M2-J against the frozen contract, including the exact domain assumptions, derivative identification, sound-speed variance/positivity, parameter endpoint recovery, midpoint identities, invertibility, matrix order, secant proof and joint limiting consistency. Inspect the audit follow-up and new expected-type checks. Replay the source-only procedure independently, compare the generated evidence and return findings with declaration/file references plus a scoped M2b verdict.

M2-E/D/O and M2-F1/F2/F3/F4/C remain unimplemented, with empty deferred bindings and no sorry/admit placeholders. Completeness, spectral projectors, absolute-speed dissipation, final numerical flux and the negative-density intermediate-state witness are later obligations. This checkpoint requests no acceptance of those results, update positivity, mesh assembly or SU2 correspondence.
