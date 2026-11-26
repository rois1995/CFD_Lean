# FVP proof map

[Frozen contract](../specifications/FV1D-positivity.md) · [External proposal review](../reviews/FVP/Scientific_Proposal_Review.md) · [Result binding](../specifications/FV1D-positivity-results.json)

The [positivity module](../CFDLean/Schemes/Euler/FV1DPositivity.lean) exposes the old right-face speed and proves endpoint and face positivity before division. The split-state determinant uses the existing positive-unit-area M1 flux. To combine the states, the proof tests internal energy against every trial velocity. Each test is linear in density, momentum and energy, so strict positivity survives nonnegative weights summing to one, including a zero central weight.

The public theorem applies the local bound to the assembled FV1D update. The [controls](../CFDLean/Schemes/Euler/FV1DControls.lean) specify its three speeds, the three updated states at the CFL endpoint, a singleton seam and a zero timestep. The [external source review](../reviews/FVP/Source_Review.md) found that candidate `8c9362f` faithfully realizes FVP-P. Hosted elaboration, verifier artifacts and type recording are pending.
