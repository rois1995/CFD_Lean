# Burgers B4 implementation authorization

B4 has no separate human approval. It is frozen by the agent under the standing authorization that the user gave on
2026-11-25 (full text in `specifications/Burgers-B1-approval.md`):

> I would like for you to keep pushing through the work and go on with the whole implementation without waiting for
> me. If the implementation is verified, you can open the corresponding PR and merge it after CI is green. [...] Then
> go on with your picks on PR 3 and so on.

Choices made by the agent for B4 (the user can change them later; a change needs a new contract revision):

1. Entropy stability in Tadmor's form with an entropy variable and an entropy potential, as separate flux certificates.
2. Semidiscrete, algebraic statements only: cell entropy inequality with an explicit numerical entropy flux and total
   entropy production. No fully discrete entropy inequality.
3. Burgers with the square entropy only; the entropy-conservative flux `(a² + ab + b²)/6` is added as a second flux.
4. Module folder `CFDLean/Entropy/Scalar/`, next to the entropy layer of the MC-N core, without an adapter to it.

All frozen statements were proved in a scratch file before this freeze. The trusted statement file is written by the
agent and checked by a separate review agent; human review is pending. No B0--B3, accepted Euler M1--M4 or M5 source
is authorized to change.
