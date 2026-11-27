# FV1D driver amendment — retire burgers1d

The owner selected removal of the standalone Burgers executable after independent acceptance of the
[unified driver](../reviews/FV1D/Driver_Acceptance.md) at `f297eeabf5a264a75ac764e68a6c847536d2e6ce`.
This amendment covers the native command, its source entry point and its regression checks.

| Prior driver obligation | Amended invocation |
| --- | --- |
| [E0-X](Burgers-E0.md#executable-e0-x), first-order Burgers with SSPRK3 | `lake exe fv1d --model burgers [N] [steps] [cfl] [--dump]` |
| [E0b-X](Burgers-E0b-amendment-1.md), MUSCL with minmod | Append `--limiter minmod` to the Burgers invocation. |
| [E0c-X](Burgers-E0c.md#executable-e0c-x), selectable MUSCL | Append `--muscl` for unlimited reconstruction or `--limiter NAME` for any of the six choices. |
| [FVA driver preservation](FV1D-array.md#kernel-and-representation) | Preserve Burgers options, defaults, SSPRK3 stepping and kernel entry points through `fv1d --model burgers`. |

`fv1d` is the sole application executable. Its root is [FVMain.lean](../FVMain.lean). The `burgers1d` Lake target and
standalone driver are removed. Existing scripts migrate by replacing `lake exe burgers1d` with
`lake exe fv1d --model burgers` and keeping their other arguments.

The uniform Burgers baseline records stdout from the pre-migration `Main.lean` at
`f537bea481ffe58337f1627ac6ab8d0a4c2d2af0`. The command headings use the new spelling. It covers defaults, a
zero-step singleton, first order, unlimited MUSCL and each named limiter, including diagnostics and final dumps.
[Reference output](../benchmarks/fv1d/burgers-uniform.txt) · [Native regression suite](../scripts/test_fv1d.py)

The original frozen contracts and acceptance records apply at their recorded revisions. The mathematical result
bindings, trusted kernels and refinement claims retain their existing scope. The regression exercises binary64 execution.
