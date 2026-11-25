# Burgers B1 implementation authorization

On 2026-11-25 the user read the three review questions of `specifications/Burgers-B1-proposal.md` with the
recommended answers and replied:

> I would choose your picks.

The three picks are:

1. the CFL hypothesis is stated per interface, not as one global bound;
2. CFL 1/2 is accepted for the bounds theorem;
3. the monotone-flux certificate is part of B1.

In the same message the user gave a standing authorization for the Burgers milestones:

> I would like for you to keep pushing through the work and go on with the whole implementation without waiting for
> me. If the implementation is verified, you can open the corresponding PR and merge it after CI is green. Before
> starting, Merge PR2. Then go on with your picks on PR 3 and so on.

Consequences recorded here:

- PR 2 (Burgers B0) was merged to `main` on this instruction, before its independent review. The B0 catalog status
  stays `pending`.
- The frozen B1 contract is `specifications/Burgers-B1.md`. It was written by the agent from the proposal and the three
  picks. Compared with the proposal it renames the certificate `Monotone` to `MonotoneFlux`, puts the B1 theorems in
  new modules so that no B0 source changes, and adds the two `step_*` theorems on a general periodic grid.
- The trusted B1 statement file is written by the agent and checked by a separate review agent. No human reviewed it
  before the merge. Human review of the trusted statements and independent review of the implementation are pending.
- Later Burgers milestones use the same authorization: proposal, contract frozen by the agent, implementation, PR,
  merge on green CI. Each contract records this in its own approval record.

No accepted Euler M1--M4 mathematical source and no M5 source is authorized to change.
