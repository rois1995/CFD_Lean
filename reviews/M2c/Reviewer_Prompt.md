# Reviewer prompt: M2c

Please independently review **M2c (M2-E/D/O)** in the private repository `rois1995/CFD_Lean`, preserving all accepted J/A/R/L contracts.

**Mathematical candidate:** `6ee9d53e79e0c6f11e75b1b387c21256572d0fcd`.

Start with [the checkpoint and evidence](https://github.com/rois1995/CFD_Lean/blob/main/reviews/M2c/README.md). The accepted inherited baseline is `c92c0f66360f85c0a3339ab9b30fc00c39ee5f93`; the frozen approval revision is `79fd2a03d7b15325c56a88ec83991b4fb4f498bb`.

Check the actual Roe matrix's 1+3+1 eigenspace dimensions, complete-basis existence, cubic identity, projector definitions/algebra/ranges/ranks, and contact/shear completeness for arbitrary tangent bases. Check that the polynomial absolute-speed operator equals R diag(abs speeds) R-inverse for every valid complete eigenbasis. Verify normal-reversal and state-swap identities, Euclidean geometry and inclusion of stationary and sonic characteristic speeds.

Verify all 37 inherited bindings/types and definition/proof sources against the accepted baseline. Inspect the extended guard, full Git binding/type diff and explicit Lean controls. Independently replay the source-only procedure and compare all deterministic audit outputs. The worker reports 58 theorem bindings, 41 Lean examples, nine Python fixtures and a complete cold-source replay with five byte-identical deterministic comparisons. Treat these as submitted evidence requiring verification.

Return a scoped M2c verdict, any conditions or blockers, and findings with declaration/file references. **M2d and full M2 acceptance are outside this review.**
