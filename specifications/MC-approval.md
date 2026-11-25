# MC authorization record

- Standing implementation authorization: `reviews/Standing_Authorization.md`.
- 2026-11-25, the user (JST_Paper_Lean session): "Go on, report when finished and we can push the CFD_Lean
  updates." and, on splitting the milestone into MC-T (toolchain port) and MC-N (numerical core + catalog):
  "Ok, go with the split but I don't plan to review it so you can proceed directly after you push".
- Consequence: MC-T is pushed on branch `core-v436` without an independent human review. Its status is
  "implemented, self-checked (AI statement review), not independently accepted; review waived by the user".
  This record does not accept any result. `main` and the accepted pins are unchanged; merging is the user's decision.
- 2026-11-25, the user: "I allow you to merge with main whenever you feel confident to do so". Merge condition used
  by the agent: verifier and fixtures green on the merge result, AI statement review without blocking findings,
  pushed branch first.
