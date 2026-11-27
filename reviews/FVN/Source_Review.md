# External source review of FVN

The owner supplied the external implementation review of [PR #43](https://github.com/rois1995/CFD_Lean/pull/43) at
`ad80a2ebd9be12be58d6a6a182a4d19b8a5cf95a` against the [frozen FVN contract](../../specifications/FV1D-nonuniform.md).

> Mandatory changes
> 1. FVN-C is over-bound in the result map relative to the frozen contract. The frozen FVN-C statement explicitly says: “Both steps are instances. Only the generic theorem is bound.” But specifications/FV1D-nonuniform-results.json currently lists three promised declarations:
>    - update_weighted_sum
>    - firstOrderStep_weighted_sum
>    - musclStep_weighted_sum
>    Only CFDLean.FV1D.Nonuniform.update_weighted_sum should be a bound FVN-C declaration. The two specialization theorems are useful and correct, but should be supporting (or simply remain unbound implementation lemmas). Correspondingly, update the FVN promised-theorem count/catalog/verifier expectations.
> 2. Final acceptance requires the trusted comparator to actually run. At reviewed head ad80a2ebd9be12be58d6a6a182a4d19b8a5cf95a, Integration CI is still in progress and the “Paranoid comparator on demand” workflow is skipped. Since the frozen milestone explicitly places FVN-B/R/M/MB and FVN-X behind the trusted Mathlib-only challenge/comparator boundary, I would not record final implementation acceptance until:
>    - Integration CI is green on the final candidate;
>    - Challenges/FV1DNonuniform.comparator.json runs in paranoid mode and passes;
>    - regenerated evidence/type pins are coherent with that candidate.
> I found no mandatory mathematical or Lean-proof correction in the implementation itself. The nonuniform update, rescaled MUSCL reconstruction, mesh-ratio use, FVN-M CFLs, Burgers 8 dt A specialization, SSP composition, and exact controls are consistent with the frozen claims.
>
> Non-blocking suggestions
> - meshRatio_needed is currently a declaration under FVN-R. I would consider treating it as a supporting/control theorem rather than a promised FVN-R theorem, since FVN-X is explicitly described as a control rather than one of the eight result IDs. This is less clear-cut than the FVN-C issue because the frozen review boundary explicitly requires the FVN-X trusted challenge, so I would not block on it.
> - Update the PR body before marking ready: it still describes Task 1 as done and the remaining implementation as “Next,” whereas the current head already contains the complete implementation, controls, trusted challenge, result map, and verifier integration.
> - The architectural separation requested before implementation was handled correctly: Nonuniform.lean owns the reconstruction-independent update, while the slope/back-forward-difference/face-state machinery lives in NonuniformMuscl.lean, explicitly documented as MUSCL-specific. Keep that split unchanged.
> - The stronger n-step SSPRK2/SSPRK3 results are acceptable, but the proof map should continue making clear that the frozen contract only requires one SSP step; the stronger theorem is an implementation strengthening, not a change in scientific scope.
>
> Independent external reviewer conclusion
>
> REQUEST CHANGES — LIMITED TO RESULT BINDING / ACCEPTANCE EVIDENCE.
>
> At source level, I find PR #43 mathematically and architecturally sound at:
>
> ad80a2ebd9be12be58d6a6a182a4d19b8a5cf95a
>
> The implementation faithfully realizes the substantive mathematics of FVN-U, FVN-K, FVN-C, FVN-A, FVN-B, FVN-R, FVN-M and FVN-MB, including the nonuniform geometry, local affine reconstruction, scalar stability conditions, one-cell/zero-step edge cases, and the three exact controls.
>
> I do not recommend final implementation acceptance yet because the FVN-C result map contradicts the frozen instruction that only the generic conservation theorem be bound, and the required paranoid trusted-statement comparator has not run successfully on the reviewed candidate.
>
> After correcting the FVN-C binding and obtaining green Integration CI plus a passing paranoid FVN comparator on the resulting candidate, I would expect to accept PR #43 without another scientific re-review, provided the mathematical implementation files and theorem statements are otherwise unchanged.

Final implementation acceptance is pending the two mandatory items above.
