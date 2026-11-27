# E1 proposal — a binary64 budget for one Burgers step

**Status: proposed for independent review.** The first target is an *a posteriori* check of one observed uniform-grid
Forward Euler update. A caller chooses an absolute error budget before the comparison. This is useful for small
reference runs where exact replay is affordable. An a priori error bound computed from input magnitudes alone is a
different deliverable.

## Inputs and reference

Use a nonempty periodic array of binary64 cell values, finite binary64 `dx > 0` and `dt ≥ 0`, and a nonnegative
rational budget `b`. Interpret each finite input as its exact represented rational, including subnormals. Both signs
of zero represent zero. Reject NaNs and infinities. The mathematical input consists of these represented values:
error in sampling an analytic function, parsing a decimal, or choosing the timestep is a separate question.

The observed output must be the result of the pinned uniform Burgers `CFDLean.Exec.eulerStepArray dx dt u` instantiated
with Lean `Float`. The executable checker should call that kernel itself. Compute the exact reference by instantiating
the same kernel with rational arithmetic. In particular, the update evaluates
`u + dt * (-(fluxRight - fluxLeft) / dx)`. A differently associated machine formula can give different bits.
[Kernel](../CFDLean/Exec/Kernel.lean) · [E0 real refinement](../CFDLean/Exec/Refinement.lean)

## Proposed obligations

1. Decode the pinned Lean binary64 model into a signed dyadic value or a non-finite result. State the interpretation
   of zero, subnormal and normal encodings. Link the interpretation to the model used by the pinned toolchain.
2. Prove that casting the rational step to the reals agrees cell by cell with the E0 real step on the represented
   inputs. Together with E0 this fixes the real reference, including seam indexing and singleton behavior.
3. Accept a step only if all outputs are finite, sizes match, and every absolute difference from its exact reference
   is at most `b`. Prove the corresponding real per-cell inequality. Exercise zero budget, a nonzero measured error,
   a too-small budget and a non-finite output. Reject invalid inputs even for a zero timestep.
4. Distinguish the logical `Float` result from native observation. A claim about a native run assumes faithful
   execution of the compiled kernel and faithful recovery of its bits. A native regression exercises that boundary.
   The certificate concerns final cell values, and makes no claim that every intermediate is normal.

Scope ends after one first-order step. The Burgers CLI composes three Forward Euler stages with rounded SSPRK3
coefficients. Its run needs a separate composition and input-error analysis. Euler, reconstruction and an
unconditional bound for all finite inputs are outside this proposal.

## Review decision

Assess the value of an a posteriori budget, the input interpretation, the precise kernel and the native trust
assumptions. Recommend freezing this scope, request specific changes, or reject it. Draft proofs and controls in the
review stack are feasibility evidence. A freeze, result bindings and an independent implementation verdict follow
separately under the [milestone workflow](../CONTRIBUTING.md#milestone-workflow).
