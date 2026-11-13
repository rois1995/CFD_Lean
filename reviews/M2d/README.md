# M2d and complete M2 review checkpoint

Worker submission, 2026-11-13. M1 and M2a/M2b/M2c are independently accepted. This submission implements the final approved M2-F1/F2/F3/F4/C obligations and requests both a scoped M2d verdict and a composed full-M2 verdict. Independent acceptance is pending; M3 has not started.

- Mathematical candidate: [`ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`](https://github.com/rois1995/CFD_Lean/commit/ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1).
- Accepted inherited baseline: [`6ee9d53e79e0c6f11e75b1b387c21256572d0fcd`](../M2c/Acceptance.md), covering all 58 J/A/R/L/E/D/O bindings.
- Frozen scientific contract: [M2.md at the candidate](https://github.com/rois1995/CFD_Lean/blob/ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1/specifications/M2.md), unchanged from approved revision `79fd2a03d7b15325c56a88ec83991b4fb4f498bb`.
- [Qualified declaration map](https://github.com/rois1995/CFD_Lean/blob/ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1/specifications/M2-results.json), [complete obligation/proof map](https://github.com/rois1995/CFD_Lean/blob/ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1/references/M2d.md), [new mathematical module](https://github.com/rois1995/CFD_Lean/blob/ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1/CFDLean/Flux/Roe/Flux.lean), [explicit checks](https://github.com/rois1995/CFD_Lean/blob/ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1/StatementChecks.lean).

## Delivered contracts

| ID | New qualified declarations (prefix CFDLean.Roe) | Result |
| --- | --- | --- |
| M2-F1 | numericalFlux_consistency | Equal-state flux equals the actual M1 physicalFlux for every S. |
| M2-F2 | numericalFlux_reverse | State swap and area reversal negate every conserved output component. |
| M2-F3 | numericalFlux_zero; numericalFlux_scale | Explicit zero-area branch and nonnegative scaling, including b=0 and S=0. |
| M2-F4 | numericalFlux_upwind_left; numericalFlux_upwind_right | Actual left/right physical flux if q>=c or q<=-c, including equality. |
| M2-C | witness_intermediate_coordinates; positivity_counterexample | Actual same-projector intermediate vector, admissible endpoints, positive averaged sound square and strictly negative intermediate density. |

The public numericalFlux uses accepted M1 states and accepted encode/decode. Its nonzero branch is half the sum of the actual M1 integrated fluxes minus area(S)/2 times the accepted M2c dissipation at the Euclidean unit normal, applied to the R-L jump. The explicit zero branch avoids unit-normal evaluation at S=0. The central term already contains area, and dissipation contains exactly one area factor. It uses the original Roe method without entropy correction or fallback.

The physical domain is common gamma>1 and both endpoints M1-admissible. Upwinding also requires nonzero S. Consistency, reversal, zero and scaling have stronger raw algebraic types, which imply the approved physical claims without supplying physical meaning to invalid inputs. The upwind proof derives D=+/-A from accepted spectral reconstruction and sound positivity, then uses the accepted integrated secant identity. No desired conclusion is assumed.

The receding-state witness is formed through M1 primitive conversion at gamma=2, rho=1, p=1/2, velocities -2 and +2 in x. Its intermediate state is defined by the identical minus projector used by dissipation. The proved vector is (1-2/sqrt(3),0,0,0,5/2-2sqrt(3)), with negative density. This refutes unconditional positivity of that approximate Riemann intermediate state; it does not claim a particular finite-volume update fails under a specified CFL bound.

## Inheritance, evidence and complete M2 closure

All 12 approved result IDs are populated. There are 66 promised bindings: 58 inherited and 8 new. All accepted definition/proof sources, scientific specifications, Integrity.lean, KernelAudit.lean, toolchain and dependency pins remain byte-identical to the accepted baseline. Only the import-only umbrella changes to export the flux module.

The inherited guard now freezes all seven accepted groups J/A/R/L/E/D/O and all 58 ordered bindings, stages and elaborated theorem types against 6ee9d53. The nine regression fixtures reject substitutions, changed stages and weakened types across these groups. The [literal full-index Git diff](bindings-and-types.patch) compares the binding map and verification.json with that accepted revision. The candidate's [inherited types](https://github.com/rois1995/CFD_Lean/blob/ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1/evidence/inherited-types.json), [complete type diff](https://github.com/rois1995/CFD_Lean/blob/ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1/evidence/binding-type-diff.json) and [binding-file diff](https://github.com/rois1995/CFD_Lean/blob/ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1/evidence/bindings-diff.patch) expose all claims; exactly eight accepted types are null because those claims are new.

The audit inventories 507 qualified records. Its 400 safe mathematical roots reach 20,183 declarations, precisely propext, Classical.choice and Quot.sound, and no unsafe declaration. The 71 unsafe compiler/executable auxiliaries and 36 metadata-only names remain visible as non-roots. The 56 Lean examples retain all 41 prior examples and add 15 flux/witness interface and exact controls. They include equal moving and oblique states, stationary contact/shear and both sonic upwind directions, with states formed by M1 primitive conversion. Example count is supporting coverage evidence, not independent validation of the intended physics.

Full M2 closure is requested by composition of accepted J/A/R/L/E/D/O with these new F1/F2/F3/F4/C results. The source/proof map records each approved ID and its role. No M2 obligation is intentionally deferred. The worker does not supply independent scientific acceptance.

## Source-only replay

**Passed:** the worker completed the exact candidate replay from a clean detached checkout without .lake. All nine dependency source revisions were fetched afresh, both binary-cache controls were enabled, and pinned widget assets were built locally. All 32 source hashes passed before and after the build. The full build, nine fixtures, 56 Lean examples, 66 bindings, 58 inherited types and nine dependency pins passed. Only evidence/build.log changed in the fresh tracked checkout.

All five deterministic files match the exact candidate byte for byte. See [the comparison log](../../evidence/M2d-source-replay/audit-comparison.log), [complete replay logs](../../evidence/M2d-source-replay/), [replay record](../../evidence/M2d-source-replay/replay.json) and [archive checksums](../../evidence/M2d-source-replay/SHA256SUMS). Verify archived file hashes by running sha256sum -c SHA256SUMS from that archive directory. This was a worker reproduction, not an independent reviewer run.

From a fresh clean full clone detached at the exact candidate, with no .lake, place Lean/Lake 4.19.0, Git, Python 3, Node/npm, sha256sum and realpath on PATH, and run:

```bash
bash scripts/reproduce.sh ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1 /outside/checkout/M2d-replay-logs
```

The script fetches all nine pinned dependency source trees, disables both binary-cache mechanisms, builds pinned ProofWidgets JavaScript locally from its npm lockfile, checks the original source hashes before regeneration, runs the nine fixtures and full verification, and compares all five deterministic outputs with the exact candidate byte for byte. The build transcript may vary by environment. The Git clone must contain the historical accepted/approved objects used by the guard.

## Reviewer handoff and limits

Use [the ready-to-send reviewer prompt](Reviewer_Prompt.md). Return scoped M2d and composed-M2 verdicts, blockers or conditions, and findings with declaration/file references. Preserve the independently accepted earlier stages and frozen approval criteria. Any new milestone or change of scientific method needs its own decision.

No entropy stability, finite-volume update positivity, floating-point/solver correspondence, mesh assembly, boundary treatment or time update is claimed. M3 has not started.
