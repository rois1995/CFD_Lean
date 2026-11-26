# Burgers B3b implementation authorization

On 2026-11-26, after the merge of E0b, the user wrote:

> I would prefere the MUSCL reconstruction to be unlimited by default and then  a limiter can be added on top. Is this
> formulation a problem? Then, implement the other widely used limiters too

The agent answered that the formulation is not a problem (the B3 reconstruction already takes any slope function, and
conservation and constant states are proved for every slope) and started B3b. The standing authorization of 2026-11-25
(`specifications/Burgers-B1-approval.md`) covers the process: contract frozen by the agent, implementation, PR, merge
on green CI.

Choices made by the agent for B3b (the user can change them later; a change needs a new contract revision):

1. The unlimited slope is the central difference `(a + b)/2`.
2. A limiter is a factor `ψ(a, b)` that multiplies the unlimited slope (the structure of production codes); the
   classical slope forms are proved equal to the factor forms.
3. "Widely used limiters": minmod, MC, superbee, van Leer, van Albada. Koren, ospre, Venkatakrishnan and
   Barth--Jespersen are not included.
4. One certificate `SlopeBounded θ` for all of them; CFL hypothesis `(4 + 2θ) · dt · max(|m|, |M|) ≤ dx`. Not sharp.
5. The B3 sources do not change; B3b adds modules. Limiters in the executable kernel are a separate later milestone.

All frozen statements were proved in a scratch file before this freeze (by a helper agent, from statements written by
the agent; no statement and no constant had to change). The trusted statement file is written by the agent and
checked by a separate review agent; human review is pending. No B0--B4, E0, E0b, accepted Euler M1--M4 or M5 source
is authorized to change.
