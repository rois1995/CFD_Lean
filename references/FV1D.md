# FV1D — first-order periodic Burgers and Euler step

The [contract](../specifications/FV1D.md) was frozen at `e0dcc57` after
[independent proposal review](../reviews/FV1D/Scientific_Proposal_Review.md).
[Result bindings](../specifications/FV1D-results.json) · [Implementation authorization](../specifications/FV1D-approval.md)

The [shared method](../CFDLean/Discrete/Periodic/Rusanov.lean) takes the model flux and endpoint dissipation
speed as functions. A real scalar acts on a conserved state in a real module. Both faces use old cell averages.
The `step_sum` proof reindexes the predecessor-face sum using the existing periodic grid equivalence.
The theorem applies to the entire state and requires no admissibility or CFL hypothesis.

| Result | Binding and proof |
|---|---|
| FV1D-B | [Burgers adapter](../CFDLean/Schemes/Burgers/FV1D.lean). `fv1d_face_eq` identifies the shared face with the existing B0 Rusanov evaluator. `fv1d_step_eq` proves cellwise equality with the assembled B0 Forward Euler step. |
| FV1D-F | [Euler adapter](../CFDLean/Schemes/Euler/FV1D.lean). `encode` and `decode` identify M1 `Conservative 1` with its three conserved coordinates. `flux_m1` recovers the integrated flux on the positive unit face. Equal-state consistency follows from `FV1D.face_self`. |
| FV1D-K | The Euler constant-field theorem specializes the common `FV1D.step_constant` and decodes the result. |
| FV1D-C | Evaluation at coordinates 0, 1 and 2 of the state-sum equality gives the volume-weighted density, momentum and energy balances. The public theorem carries the reviewed physical hypotheses. |

The [three-cell control](../CFDLean/Schemes/Euler/FV1DControls.lean) uses the actual endpoint speed, M1 physical
flux and assembled step. It checks the three oriented mass fluxes, including the wraparound face, and the nine
updated components against exact rational values. The control adds evidence for the four frozen claims.

Independent implementation acceptance is pending.
