# Independent review of the Burgers driver retirement

Review the candidate SHA identified in [PR #49](https://github.com/rois1995/CFD_Lean/pull/49) against its base
`11b4fb060341c0cfb61208694c2031d32b428abe`. The [previous verdict](Driver_Acceptance.md) accepted the unified
driver. This review covers the [retirement amendment](../../specifications/FV1D-driver-amendment.md).

1. Check that Lake exposes one solver executable, that callers migrate to `fv1d --model burgers`, and that the
   obsolete executable, driver implementation and parser switch are gone.
2. Compare the recorded uniform diagnostics and dumps with the pre-migration driver at
   `f537bea481ffe58337f1627ac6ab8d0a4c2d2af0`. Check defaults, SSPRK3, unlimited reconstruction and all six limiter
   choices. Review the explicit-width and Euler tests and the Integration CI result for the candidate.
3. Check that the amendment maps E0-X, amended E0b-X, E0c-X and the FVA driver clause. Compare theorem bindings,
   trusted source hashes, raw-type pins and historical verdicts with the base revision.

Return accept, accept with mandatory fixes, or reject. Give the reviewed SHA and distinguish mandatory findings
from optional suggestions.
