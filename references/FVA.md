# FVA proof map

[Frozen contract](../specifications/FV1D-array.md) · [External proposal review](../reviews/FVA/Scientific_Proposal_Review.md) · [Result bindings](../specifications/FV1D-array-results.json)

The [kernel](../CFDLean/Exec/FV1D.lean) builds an output of the old size and uses the existing E0 successor and predecessor index bounds for each old-state lookup. Its coefficient operations are multiplication, division and a supplied half. State operations, flux and endpoint speed come from the model. Euler takes square root through its speed adapter.

In the [refinement module](../CFDLean/Exec/FV1DRefinement.lean), samples reads a periodic field in increasing residue order. The inverse representation via samples_entries covers every positive-size input array. The stencil identity transports both modular indices to ZMod. FVA-B specializes this result and compares with the original E0 operation order over the reals. FVA-E identifies the executable model with the M1 positive-unit-face flux and FV1D endpoint maximum, then compares the three stored coordinates.

The [exact controls](../CFDLean/Exec/FV1DControls.lean) cover the nine Euler outputs, a nonconstant Burgers comparison, empty and singleton arrays, and zero timestep. The [native smoke program](../scripts/FV1DSmoke.lean) exercises both concrete models. Hosted build, controls, verifier artifacts, type recording and independent implementation review are pending.
