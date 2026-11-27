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

## Follow-up on the shared 1D reconstruction

Review the [step 9 proposal](../../../roadmap/NEXT.md#step-9--a-second-1d-reconstruction-family) and its
implementation separately. The implementation chooses scalar Jiang–Shu WENO5 on uniform cell averages.
Check that the generic interface ties a reconstruction to its mesh, orders the two owners' states at the face,
and feeds the existing FVN update. Check MUSCL step equality for an arbitrary flux and limiter. For WENO, verify the
three indicators and candidates, the positive normalization, quadratic exactness, and both traces at the
asymmetric wrap from cell 5 to cell 0.
Review constant preservation and the hypotheses of width-weighted conservation separately from accuracy.
Replay with `lake build --wfail ReviewCases.Reconstruction`. Give the exact revision and any mandatory changes.

## Four implementations after the reconstruction roadmap

1. Review the graded WENO formula in width units of the owning cell. Check the three moment fits, the
   integrated smoothness on that cell, the positive ideal weights and equal-width reduction. Replay both
   rational traces across the graded seam with `lake build --wfail ReviewCases.GradedWeno`.
2. In the Burgers integration check face ownership, the exact-real Forward Euler refinement and the new
   reconstruction at all three SSPRK stages. Replay `lake build --wfail CFDLean.Exec.WenoRefinement fv1d`.
3. For Euler, check conservative-component minmod and WENO, their paired fallback and the runtime check
   after each full step. Replay `lake build --wfail ReviewCases.EulerReconstructedStep`. Both methods have
   a control where just one raw face has negative pressure.
4. Run `python3 scripts/test_fv1d.py -v` after building `fv1d`. Inspect the independent moment solve for
   WENO, the three-component Euler flux replay and the 18 model/scheme/mesh combinations. Report any
   mandatory changes against the exact candidate in each draft PR.

The CLI uses WENO regularization `1e-6`. Exact-real proofs and native regression tolerances have different scopes.
The stack leaves fully discrete Euler positivity, a general convergence rate and binary64 certification for review
in their own milestones.
