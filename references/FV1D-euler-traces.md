# Uniform Euler MUSCL proof map

The [frozen scope](../reviews/FV1D/Uniform_Euler_Trace_Freeze.md) covers strict density and pressure
at the two faces of an admissible mean. The [production module](../CFDLean/Exec/EulerTraces.lean)
uses a componentwise slope and a single decision for both endpoints. Its supporting theorem
`admissible_iff_m1` identifies the predicate with the existing conservative-state admissibility.
Full-update positivity needs a separate numerical result.

| Result | Declaration | Claim |
|---|---|---|
| FVT-A | `face_admissible` | Every oriented face receives two admissible selected traces when all means are admissible. |
| FVT-A | `face_admissible_m1` | Both real face states satisfy M1 conservative-state admissibility. |
| FVT-M | `pair_sum` | The selected pair sums componentwise to twice its parent mean. |
| FVT-R | `retain_raw` | An admissible raw pair is retained exactly. |
| FVT-K | `face_constant` | Every face reconstructs the constant pair for a limiter that vanishes at zero. |

The [rational controls](../benchmarks/ReviewCases/EulerTraces.lean) exercise the negative-pressure
counterexample, retained nonconstant traces and the periodic singleton.
