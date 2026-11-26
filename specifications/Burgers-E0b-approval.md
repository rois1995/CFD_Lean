# Burgers E0b implementation authorization

On 2026-11-26 the agent reported the night's work and offered two next steps: "A MUSCL array kernel (my pick). It
extends E0 to the second-order scheme and reuses the E0 proofs." or "B5, paper correspondence." The user replied:

> A

The standing authorization of 2026-11-25 (`specifications/Burgers-B1-approval.md`) covers the process: contract frozen
by the agent, implementation, PR, merge on green CI.

Choices made by the agent for E0b (the user can change them later; a change needs a new contract revision):

1. A new kernel module; the E0 kernel, the class `Scalar` and their pinned hashes do not change.
2. Minmod written with `max`, negation, zero and addition only, because `Scalar` has no order relation.
3. The limiter is minmod only. Forward Euler, SSPRK2 and SSPRK3; the executable uses SSPRK3.
4. The trusted statement file imports the E0 kernel, the real instance and the MUSCL kernel as hash-pinned inputs.
5. The CFL hypothesis of the transfer theorems is the B3 one, `6 · dt · max(|m|, |M|) ≤ dx`. It is not sharp.

All frozen statements were proved in scratch files before this freeze (by a helper agent, from a design written by the
agent). The trusted statement file is written by the agent and checked by a separate review agent; human review is
pending. No B0--B4, E0, accepted Euler M1--M4 or M5 source is authorized to change, except the driver `Main.lean`,
which is not verified.
