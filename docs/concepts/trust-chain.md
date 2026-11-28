# Trust chain

| Artifact | What it provides |
| --- | --- |
| Scientific method definition | The reviewed scheme, variables, orientations, hypotheses and promised results. [FV1D contract](../../specifications/FV1D.md) |
| Formal mathematical result | A Lean statement that expresses one claim under its hypotheses. [Burgers trusted statement](../../CFDLean/Verification/BurgersB0Challenge.lean) |
| Proof implementation | A checked proof and, where applicable, a bridge to the trusted statement. [B0 result bindings](../../specifications/Burgers-B0-results.json) · [B0 proof map](../../references/Burgers-B0.md) |
| Executable kernel | Arithmetic and traversal over a concrete representation. [FV1D array kernel](../../CFDLean/Exec/FV1D.lean) |
| Exact-real refinement | Equality or correspondence between the kernel interpreted over ℝ and the mathematical operator. [FV1D array refinement](../../CFDLean/Exec/FV1DRefinement.lean) |
| Machine arithmetic evidence | Bounds and domain conditions for specified operations under a concrete arithmetic model, plus bridge assumptions where the native runtime enters. [E1 scope and evidence](../../references/E1.md) |
| Runtime driver | Parsing, initialization, backend selection, time loop, diagnostics and I/O. [FV1D driver](../../FVMain.lean) |
| Benchmark or control | Finite worked cases, negative controls or independent replay under recorded inputs and tolerances. [Density-wave benchmark](../../benchmarks/fv1d/README.md) |

An exact-real theorem covers the hypotheses and operator in its statement. A native Float run has its own arithmetic obligations, even when both instantiations share the same traversal. A benchmark supports a concrete observation, and a formal error bound requires its own statement and proof.

Use the [theorem catalog](../../catalog/README.md) to find promised declarations, the [comparator configuration](../../Challenges/BurgersB0.comparator.json) to locate the trusted checking boundary, and the [independent implementation verdict](../../reviews/Burgers-Implementation/Review.md) to interpret acceptance. The [capability map](../CAPABILITIES.md) summarizes these statuses at the current revision.
