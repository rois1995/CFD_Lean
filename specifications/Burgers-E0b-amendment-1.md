# Burgers E0b amendment 1: executable flag after E0c

Date: 2026-11-26. Scope: E0b-X only. The frozen contract `specifications/Burgers-E0b.md` stays unchanged.

The frozen E0b-X text says that `burgers1d --muscl` runs `musclSsprk3StepArray` (MUSCL with minmod). E0c (contract
decision 5, approval item 1) changed the driver: `--muscl` alone now runs the unlimited scheme, and the limiter is
chosen with `--limiter NAME`.

From E0c on, E0b-X is superseded by E0c-X:

- the E0b minmod run is `burgers1d ... --limiter minmod`;
- it runs `limiterSsprk3StepArray .minmod`, which equals `musclSsprk3StepArray` by `rfl` for every arithmetic
  (`CFDLean/Exec/LimiterRefinement.lean`);
- its note line gives the same proved hypothesis, `cfl <= 1/6`, for real arithmetic.

No E0b theorem, kernel or trusted statement changes. `specifications/Burgers-E0b-results.json` records the current
flag and points to this amendment. The implementation review recorded this as the condition for E0b acceptance
([review](../reviews/Burgers-Implementation/Review.md)).
