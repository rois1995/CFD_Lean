# Add a time integrator

1. Put generic stage composition in [Time](../../CFDLean/Time/SSP.lean). Consume the existing [Forward Euler step](../../CFDLean/Time/ForwardEuler.lean) or spatial operator. Keep model- and mesh-specific CFL reasoning at the scheme boundary.
2. Freeze a new integrator's stage formula, coefficients, timing and promised stability claims. State stage CFL, convexity or domain hypotheses explicitly. The [B2 scope](../../specifications/Burgers-B2.md) separates generic SSP arguments from Burgers instantiations.
3. Prove exact-real stage identities and the claimed invariant, constant-state, conservation or admissibility transfer. A formal order claim needs its own assumptions and proof.
4. Reuse the spatial array kernel at every stage. If the mode is executable, prove composition of the stage refinements and keep adaptive-step selection in the driver where appropriate. Add zero-step, constant-state and independent multi-stage replay controls with explicit time and tolerances.
5. Bind the results, update the catalog and integrator capability, and run the [local validation commands](../getting-started.md).
