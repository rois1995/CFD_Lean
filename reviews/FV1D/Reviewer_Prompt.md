# FV1D independent implementation review

Review mathematical and evidence candidate `c8a964e35a4b34a95fa50d2e43b4b036a0e4af38` against the
[contract](../../specifications/FV1D.md) frozen at `e0dcc57`. The [result map](../../specifications/FV1D-results.json)
gives the four public theorem names and the [proof map](../../references/FV1D.md) identifies the implementing modules.

1. Trace both old-state face evaluations through the common Rusanov and Forward Euler definitions.
   Check that the speed is scalar and that all arithmetic on jump vectors and fluxes has the intended meaning.
2. For FV1D-B, follow equality to the actual B0 assembled update on every supported grid and state, including
   one cell and zero time step. For FV1D-F, trace the round trip through M1 `Conservative 1`, the positive
   unit-area flux and the endpoint speed from M1 density, momentum and pressure.
3. For FV1D-K and FV1D-C, check constant-state preservation and the projection of the reindexed state sum
   onto all three component integrals. Compare the public quantifiers with the frozen rows, including every
   domain hypothesis.
4. Independently recompute the three right-face mass fluxes and all nine updated cell components. Confirm
   that the Lean control uses the assembled Euler step, including the wraparound face.
5. Inspect the catalog bindings, expected types in `StatementChecks.lean`, kernel inventory and changes to
   the type pin. Compare with the hosted verification logs on [PR #26](https://github.com/rois1995/CFD_Lean/pull/26).
   For a replay, run the PR integration workflow on the candidate and use the B0 paranoid comparator configuration
   `Challenges/BurgersB0.comparator.json` for the reused Burgers challenge.

Report the candidate SHA, the result IDs covered, any mandatory findings, and the independent implementation
verdict. The earlier proposal verdict authorized the scope.
