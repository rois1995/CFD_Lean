# P1 approval record

- 2026-11-25: the user approved `specifications/P1-proposal.md` with decisions **D1 = A** (real median-dual geometry:
  d = 3 through CFD_Lean, d = 2 by own code) and **D2 = A** (prove the two-state best-constant statement P1-1.6).
- CFD_Lean pin for D1: `3a586a42546cba1784cc79269e3f9d1c5d843f0c` (accepted M4 mathematical commit, from
  `CFD_Lean/specifications/accepted-M4.json`). `CFDLean/Geometry` is identical at CFD_Lean HEAD `be20e81`.
- 2026-11-25, answers of the solver session on the paper notes (see `PAPER_GAPS.md` G1-G4), accepted by the user:
  - P1-1.6 is a best-constant statement.
  - Item 3: the sensor is a fixed input built from the π-weighted sums, not a mean over splits.
  - Item 3: the boundary part of Λ_i is a given non-negative split-independent input `bnd i`.
  - Item 3: π_ik > 0, λ̂_ik > 0, Λ_i > 0, Λ_k > 0 are explicit hypotheses.
- Next: frozen specification `specifications/P1.md` with statements elaborated in Lean (as `Prop` definitions, no
  `sorry`).
- 2026-11-25: the user answered "freeze": the statements of commit `e3f6a11` are frozen. Hashes of the statement and
  definition files: `specifications/P1-frozen.sha256`. Any later change to these files needs a new approval entry.
- 2026-11-25: independent review (`reviews/P1/Review.md`): Accept with conditions, no blocking finding. Follow-up
  without statement changes: pins hashed (`P1-pins.sha256`), binding cross-check, S4 labels, report scope (S1).
- 2026-11-25: G1-G4 fixed in the paper (`Handbook/paper1/paper1.tex`, sha256 `32e1f260…`). The user approved
  `specifications/P2-proposal.md` with **D1 = A** (P2 = items 6-10; items 11-13 later as P3) and **D2 = A**
  (`lem:dissgeom`(d) stated exactly for quadratic q).
- 2026-11-25: the user said "you can start the proofs" after reading the P2 statements: the 32 statements of commit
  `64244e4` are frozen. Hashes: `specifications/P2-frozen.sha256`.
- 2026-11-25: after the P2 review the user chose A (stronger statements) and answered "freeze" for
  `Paper1/Spec/Addendum2.lean` (commit `be94d0c`): P2-8.0b, P2-9.2b, P2-10.8b, P2-10.8c. Hash added to
  `specifications/P2-frozen.sha256`.
- 2026-11-25: the user approved `specifications/P3-proposal.md` with **D1 = A** (items 11-14, staged) and **D2 = A**
  (full geometric chain for `lem:avg`). Freeze in two stages: stage 1 = items 12, 13 and P3-11.1-11.3; stage 2 =
  the mixed-mesh assembly (rest of item 11) and item 14.
- 2026-11-25: the user answered "freeze" for P3 stage 1 (commit `0dde547`). Hashes: `specifications/P3-frozen.sha256`.
  The user asked that from now on I formalize, self-check and prove without stopping for approvals, and come back
  only when the work is done, with the proposed next steps.
- 2026-11-25: P3 stage 2 self-frozen (user instruction: formalize, self-check, prove without stopping). Statement
  review `reviews/P3/StatementReview-stage2.md`: no blocking finding; S2 fixed (2D: P3-11.2b, 11.4b), minor docstring
  fixes done. S1 (cell geometry ⇒ side balance not formal) becomes stage 3 (P3-11.7 affine reference cells, P3-11.8
  assembly), to keep D2 = A.
- 2026-11-25: P3 stage 3 self-frozen: `Paper1/Mixed/Assembly.lean`, `Paper1/Spec/Item11c.lean` (P3-11.7 geometry of
  pulling splits on affine cells, P3-11.8 conforming affine mixed mesh ⇒ facet balanced). Self-check: P3-11.7
  tested numerically on 20 random affine images per cell type (34,560 side tests, all pass).
- 2026-11-26: P4 (`specifications/JST1/P4-proposal.md`, items 15-18: `prop:wallJST`, `prop:consistency`(b),(c),
  `prop:sstpde` PDE form, `lem:sstentropy` Hessian form) self-decided and self-frozen under the user's instruction for
  this cycle (formalize, review, freeze, prove, audit, commit without mid-batch approvals). Decisions D1-D6 as in the
  proposal. Independent statement review `reviews/JST1/P4-statement-review.md`: no blocking finding; S2 fixed (Π^(4)
  split added to P4-15.4), S1 documented (P4-16.2 abstract; G6), minor docstring fixes (M1). Proof drafts were written
  while the review ran; the statements changed after the review only by these fixes, and are frozen as reviewed:
  `CFDLean/Papers/JST1/Spec/Item15.lean` .. `Item18.lean`, hashes in `specifications/JST1/frozen.sha256`.

## P5 (items 19-20), self-frozen 2026-11-26

Under the user's instruction of 2026-11-26 (whole cycle authorized without approvals in between). Proposal
`P5-proposal.md`; independent statement review `reviews/JST1/P5-statement-review.md` (no blocking finding; findings 1
and 2 fixed before the freeze). Frozen: `CFDLean/Papers/JST1/Spec/Item19.lean`, `Item20.lean` (hashes in
`frozen.sha256`). No earlier frozen file changed.

## P6 (item 21), self-frozen 2026-11-26

The user chose this batch (simplex integral) after P5; the cycle runs under the same authorization. Proposal
`P6-proposal.md`; independent statement review `reviews/JST1/P6-statement-review.md` (no blocking finding; docstring
findings fixed before the freeze). Frozen: `CFDLean/Papers/JST1/Spec/Item21.lean`. No earlier frozen file changed.
