# Burgers B2 implementation authorization

B2 has no separate human approval. It is frozen by the agent under the standing authorization that the user gave on
2026-11-25 (full text in `specifications/Burgers-B1-approval.md`):

> I would like for you to keep pushing through the work and go on with the whole implementation without waiting for
> me. If the implementation is verified, you can open the corresponding PR and merge it after CI is green. [...] Then
> go on with your picks on PR 3 and so on.

Choices made by the agent for B2 (the user can change them later; a change needs a new contract revision):

1. SSPRK2 and SSPRK3 in Shu-Osher form, generic over a one-step map on a real vector space.
2. Mathlib `Convex` and `ConvexOn` for invariant sets and functionals.
3. One time step for all steps, with the CFL hypothesis `2 · dt · max(|m|, |M|) ≤ dx` from the bounds of the initial
   state (CFL 1/2 comes from the B1 bounds theorem).
4. Results on any periodic grid; no separate `ZMod N` copies.
5. No order-of-accuracy claim for the Runge-Kutta methods.

All frozen statements were proved in a scratch file before this freeze. The trusted statement file is written by the
agent and checked by a separate review agent; human review is pending. No B0, B1, accepted Euler M1--M4 or M5 source
is authorized to change.
