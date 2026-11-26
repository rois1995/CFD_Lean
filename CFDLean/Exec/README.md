# Executable Burgers kernels

| Milestone | Computable kernel | Exact-real refinement |
|---|---|---|
| [E0](../../references/Burgers-E0.md) | [Kernel](Kernel.lean), first-order Rusanov | [Refinement](Refinement.lean) |
| [E0b](../../references/Burgers-E0b.md) | [MusclKernel](MusclKernel.lean), minmod MUSCL | [MusclRefinement](MusclRefinement.lean) |
| [E0c](../../references/Burgers-E0c.md) | [LimiterKernel](LimiterKernel.lean), selectable MUSCL limiter | [LimiterRefinement](LimiterRefinement.lean) |

[RealScalar](RealScalar.lean) and [RealScalarSign](RealScalarSign.lean) instantiate the arithmetic interfaces over `ℝ`.
The refinement proofs connect arrays using those instances to the periodic schemes and transfer the stated guarantees.
The kernel is arithmetic-polymorphic through `Scalar α`. The native driver selects `Float` (binary64) and handles
initialization, parsing and diagnostics. Its arithmetic and output are outside the exact-real proof boundary.
[Driver](../../Main.lean) · [E1 backend contract](../../roadmap/NEXT.md#priority-2---e1-machine-arithmetic-strategy)

From the repository root, run the first-order scheme or select a MUSCL limiter.

```bash
lake exe burgers1d 200 200 0.4
lake exe burgers1d 200 600 0.12 --limiter vanleer
```

The positional arguments select cell count, steps and CFL number. Limiter names are `none`, `minmod`, `mc`, `superbee`,
`vanleer` and `vanalbada`. `--muscl` alone is equivalent to `--limiter none`. This unlimited scheme can overshoot.
Use `--limiter minmod` to run the E0b scheme. Add `--dump` to print the final cell values after the diagnostics.
