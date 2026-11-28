# Add an executable kernel

1. Start in [Exec](../../CFDLean/Exec/README.md). Reuse the existing state operations, array traversal and indexing checks. Keep parsing, output, initialization and backend selection in the driver.
2. Use the frozen mathematical operator as the specification. Propose and freeze a representation contract when adding new refinement promises, including storage, lengths, boundary handling, domain checks and execution scope. See the [FV1D array contract](../../specifications/FV1D-array.md).
3. Prove the representation relation and exact-real pointwise refinement over ℝ, including degenerate valid sizes. Transfer only the invariants supported by the mathematical and representation hypotheses.
4. Add paired mathematical/array examples, malformed input controls and independent replay. If there is a machine guarantee, state its backend, finite-domain restrictions, error budget and native-runtime assumptions separately. [E1 map](../../specifications/E1-results.json)
5. Update the result map, catalog and executable capability evidence. Run the [local validation commands](../getting-started.md).
