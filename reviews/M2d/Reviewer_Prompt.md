# Reviewer prompt: M2d and composed M2

Please independently review **M2d (M2-F1/F2/F3/F4/C)** and give a separate **composed full-M2 verdict** in the private repository `rois1995/CFD_Lean`.

**Mathematical candidate:** `ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`.

Start with [the checkpoint and evidence](https://github.com/rois1995/CFD_Lean/blob/main/reviews/M2d/README.md). The accepted inherited baseline is `6ee9d53e79e0c6f11e75b1b387c21256572d0fcd`, covering all 58 J/A/R/L/E/D/O bindings; the frozen approval revision is `79fd2a03d7b15325c56a88ec83991b4fb4f498bb`.

Check that the public numericalFlux assembles the actual M1 integrated physical flux and accepted M2c absolute-speed operator, with an explicit zero-area branch, Euclidean unit normal and exactly one dissipation area factor. Verify consistency, state-swap-plus-area-reversal conservation, nonnegative scaling including b=0/S=0, and both full-upwind identities under the approved physical hypotheses. Include sonic equality and stationary modes; no nonzero characteristic-speed assumption is allowed.

Check the admissible receding-state endpoints through M1 primitive conversion, positive averaged sound speed, and the intermediate state built with the identical minus projector used by dissipation. Verify its full coordinates and strictly negative density. Distinguish this approximate Riemann-state counterexample from any claim about a particular finite-volume update or CFL bound.

Verify all 58 inherited bindings, stages, theorem types and definition/proof sources against the accepted baseline. Inspect the extended inherited guard, literal full Git diff and explicit Lean controls. Independently replay scripts/reproduce.sh at the exact candidate from a clean checkout without .lake, using both cache controls and pinned dependency sources; compare all five deterministic audit outputs byte for byte. The worker's local checks report 66 bindings, 56 examples, nine fixtures, 507 inventory records and no forbidden/unsafe reachable dependency. The fresh worker source replay passed, including all 32 pre/post source hashes and five byte-identical deterministic comparisons. Treat submitted logs as evidence to verify, not independent acceptance.

Check closure of every approved M2 ID by composing the new flux contracts with accepted J/A/R/L/E/D/O. Return **(1) a scoped M2d verdict and (2) a composed full-M2 verdict**, plus any blockers/conditions and findings with qualified declarations and file references. M3, entropy correction, update positivity and SU2 correspondence are outside this review and have not started.
