# Review queue after the unified FV1D driver

Review the eight draft layers from bottom to top. For each PR use its parent branch as the diff base.
The [queue](../../../roadmap/NEXT.md#eight-step-review-queue-after-pr-50) states the scientific dependencies.
The PR descriptions give exact candidate revisions and replay commands. The production solver remains the accepted
`fv1d` driver throughout this stack.

| Layer | Review question |
|---|---|
| [1. E1 proposal](https://github.com/rois1995/CFD_Lean/pull/51) | Does a per-input, a posteriori budget meet the intended first E1 use case? Review finite-value semantics and the native trust boundary. |
| [2. Decoder](https://github.com/rois1995/CFD_Lean/pull/52) | Are signed zeros, subnormals, normal exponents and non-finite values interpreted correctly by the pinned model? |
| [3. Exact replay](https://github.com/rois1995/CFD_Lean/pull/53) | Does the rational step commute with the cast to the real E0 kernel, including periodic neighbors? |
| [4. Soundness](https://github.com/rois1995/CFD_Lean/pull/54) | Does acceptance bound every actual output against the real step for the represented inputs? Check rejection paths, sizes and the external budget. |
| [5. Controls](https://github.com/rois1995/CFD_Lean/pull/55) | Can the tests distinguish exactness, rounding, underflow and non-finite intermediate effects? |
| [6. Euler proposal](https://github.com/rois1995/CFD_Lean/pull/56) | Are the variables, two-sided cell fallback and strict face admissibility the right scope? |
| [7. Euler controls](https://github.com/rois1995/CFD_Lean/pull/57) | Check the M1 correspondence, both branches, cell-mean preservation, constants, and ownership at the periodic seam. |
| 8. Oriented triangles (this PR) | Check the sign, area and boundary conventions, the shared transfer of 6, and boundary balance on unequal cells. |

Run `lake build --wfail ReviewCases` under the repository's Lean memory cap for all draft proofs and controls.
The existing driver regressions run with `lake build fv1d` and `python3 scripts/test_fv1d.py -v`.
For each proposal recommend freeze, amend, or reject. Identify mandatory changes separately from suggestions, and
give the commit reviewed. A proposal verdict and a subsequent implementation acceptance are separate decisions.
