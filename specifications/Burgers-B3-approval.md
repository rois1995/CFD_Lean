# Burgers B3 implementation authorization

B3 has no separate human approval. It is frozen by the agent under the standing authorization that the user gave on
2026-11-25 (full text in `specifications/Burgers-B1-approval.md`):

> I would like for you to keep pushing through the work and go on with the whole implementation without waiting for
> me. If the implementation is verified, you can open the corresponding PR and merge it after CI is green. [...] Then
> go on with your picks on PR 3 and so on.

Choices made by the agent for B3 (the user can change them later; a change needs a new contract revision):

1. Limiter class: the minmod region (`MinmodBounded`). MC and superbee are excluded.
2. Stability route: Harten incremental form of the MUSCL Forward-Euler step, then the B1 lemmas and the B2 SSP
   composition. The flux needs the `MonotoneFlux` certificate and a new Lipschitz certificate on bounded states.
3. CFL hypothesis `dt · (3/2)(KL + KR) ≤ dx` in general and `6 · dt · max(|m|, |M|) ≤ dx` for Burgers with Rusanov.
   It is sufficient, not sharp.
4. No accuracy claim for the reconstruction.

All frozen statements were proved in a scratch file before this freeze (by a helper agent, from statements written by
the agent; the helper found that B3-I needs `0 ≤ KL`, `0 ≤ KR` and gave a counterexample). The trusted statement file
is written by the agent and checked by a separate review agent; human review is pending. No B0, B1, B2, accepted
Euler M1--M4 or M5 source is authorized to change.
