# Burgers E0c implementation authorization

On 2026-11-26 the user wrote:

> I would prefere the MUSCL reconstruction to be unlimited by default and then  a limiter can be added on top. Is this
> formulation a problem? Then, implement the other widely used limiters too

B3b did this for the mathematics (`specifications/Burgers-B3b-approval.md`). E0c does it for the executable kernel and
the program. The standing authorization of 2026-11-25 (`specifications/Burgers-B1-approval.md`) covers the process:
contract frozen by the agent, implementation, PR, merge on green CI.

Choices made by the agent for E0c (the user can change them later; a change needs a new contract revision):

1. `burgers1d --muscl` now means the unlimited scheme; `--limiter NAME` adds a limiter. Before (E0b) `--muscl` meant
   minmod. `--limiter minmod` gives the old result bit for bit.
2. The kernel computes limited slopes in slope form, with one sign branch for van Leer and van Albada, through a new
   class `ScalarSign`. The class `Scalar` and the older kernels do not change.
3. For the unlimited scheme only refinement and conservation are proved.
4. The trusted statement file imports five hash-pinned trusted inputs.

All frozen statements were proved in scratch files before this freeze (by a helper agent, from a design written by the
agent), and the prototype program was run: the unlimited run overshoots after the shock forms, every limited run stays
in the initial bounds. The trusted statement file is written by the agent and checked by a separate review agent;
human review is pending. No B0--B4, B3b, E0, E0b, accepted Euler M1--M4 or M5 source is authorized to change, except
the driver `Main.lean`, which is not verified.
