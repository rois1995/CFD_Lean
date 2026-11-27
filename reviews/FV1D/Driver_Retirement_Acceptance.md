# FV1D driver retirement acceptance

The independent external reviewer accepted the [retirement amendment](../../specifications/FV1D-driver-amendment.md) in
[PR #49](https://github.com/rois1995/CFD_Lean/pull/49) at the following revision.

> ACCEPT DRIVER RETIREMENT AMENDMENT for PR #49 at:
>
> 6fbbd2af020e4c2387154ff2c0dedd99ba9e8478

The reviewer found the frozen legacy-output regression and successful Integration CI sufficient evidence that
`fv1d --model burgers` preserves the accepted Burgers behavior. The review confirmed that the migration preserved
the numerical kernels, refinement proofs, trusted statements, theorem bindings and raw theorem types.
[Integration CI on the reviewed revision](https://github.com/rois1995/CFD_Lean/actions/runs/46064147094)

The reviewer asked that the transcript provenance remain prominent. Its stdout comes from the pre-migration
driver at `f537bea481ffe58337f1627ac6ab8d0a4c2d2af0`. Only the command headings were rewritten. Historical
specifications and verdicts retain the name `burgers1d` for the executable accepted at those revisions.
[Uniform Burgers transcript](../../benchmarks/fv1d/burgers-uniform.txt)

The reviewer recommended linking this decision from the roadmap and merging once ordinary branch requirements are satisfied.
