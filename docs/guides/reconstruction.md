# Add a reconstruction

1. Start with the [oriented trace interface](../../CFDLean/Discrete/Periodic/Reconstruction.lean). A reconstruction consumes geometry and field values and returns the owner-side and neighbor-side trace in the agreed orientation. Record stencil indices, seam handling, distances and exceptional cases in the scientific proposal and freeze the method-specific contract.
2. Prove exact-real constant preservation and the polynomial reproduction, limiter bounds, TVD or trace admissibility the contract promises. State width and geometry hypotheses. Use the [WENO scope](../../specifications/FV1D-WENO-reconstruction-proposal.md) and [limiter proof map](../../references/Burgers-B3b.md) for examples of different proof obligations.
3. Pass the traces to an existing numerical flux and reuse the existing conservative update. Keep the transfer signs and volume-weighted accumulation in the shared assembly.
4. If running the method is in scope, adapt the [reconstructed array kernel](../../CFDLean/Exec/ReconstructedKernel.lean) and prove exact-real refinement. Add uniform parity, a nonuniform periodic seam case, appropriate invalid-state controls and independent reference replay.
5. Update the result map, theorem catalog and the scoped reconstruction capability. Run the [local validation commands](../getting-started.md).
