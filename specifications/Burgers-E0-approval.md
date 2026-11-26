# Burgers E0 implementation authorization

E0 has no separate human approval. It is frozen by the agent under the standing authorization that the user gave on
2026-11-25 (full text in `specifications/Burgers-B1-approval.md`):

> I would like for you to keep pushing through the work and go on with the whole implementation without waiting for
> me. If the implementation is verified, you can open the corresponding PR and merge it after CI is green. [...] Then
> go on with your picks on PR 3 and so on.

The opening task text asks for this milestone: "verified mathematical Burgers scheme -> Array implementation -> proof
of one-step refinement -> native Lean executable", for example `lake exe burgers1d`.

Choices made by the agent for E0 (the user can change them later; a change needs a new contract revision):

1. E0 is done before B5 (paper correspondence). B5 needs a choice of references by the user.
2. One kernel that is generic in its arithmetic, with a `Float` instance for execution and an `ℝ` instance for the
   proof. Nothing is proved about `Float`.
3. First-order Rusanov scheme with Forward Euler, SSPRK2 and SSPRK3. No MUSCL kernel.
4. Immutable arrays built with `Array.ofFn` and `Array.zipWith`; no in-place update.
5. The trusted statement file imports the kernel and the `ℝ` instance (hash-pinned) in addition to Mathlib, because
   the statements are about that code.

All frozen statements were proved in scratch files before this freeze (by a helper agent, from a design written by the
agent), and the prototype program was run and compared with an independent Python script. The trusted statement file
is written by the agent and checked by a separate review agent; human review is pending. No B0--B4, accepted Euler
M1--M4 or M5 source is authorized to change.
