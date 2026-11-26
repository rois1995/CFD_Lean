# Roadmap: current state

Status date: 2026-11-26. Toolchain: Lean v4.36.0, Mathlib v4.36.0.

This file is a compact snapshot of what exists today. Historical detail belongs in `references/`, formal contracts in
`specifications/`, review records in `reviews/`, and theorem coverage in `catalog/`.

## Core architecture

The library is organized into layered modules:

```text
Foundations/
Geometry/
Discrete/
Entropy/
Physics/
Schemes/
Time/
Exec/
Papers/
```

The project already contains both:

- cell-centered periodic finite volume for scalar Burgers;
- node-centered median-dual finite volume for Euler.

These are treated as different realizations of shared numerical concepts rather than one universal discretization.

## Euler / Roe / median-dual line

- M1--M4 are independently accepted.
- M5 is implemented and pending independent acceptance.
- The code includes exact-real Euler state/flux machinery, Roe averages and linearization, spectral decomposition,
  Roe numerical flux, median-dual geometry, boundary transfers, residual assembly and explicit Euler stepping.
- M6 multi-step composition remains open.

## Burgers line

Merged into `main`:

- B0: composable scalar FV core, Rusanov consistency, conservation, constants;
- B1: monotonicity, TVD and bounds under CFL;
- B2: SSPRK2/SSPRK3 and multi-step stability/conservation;
- B3: MUSCL/minmod reconstruction with TVD/bounds and SSP composition;
- B4: scalar entropy certificates and semidiscrete Burgers entropy stability;
- E0: executable first-order array kernel, real-arithmetic refinement, native `burgers1d`;
- E0b: executable MUSCL array kernel, refinement, and transferred B3 guarantees.

All Burgers milestones above are implemented and merged, but independent scientific acceptance is still pending.

## Executable status

`lake exe burgers1d` currently supports:

- first-order Rusanov;
- MUSCL-minmod + Rusanov;
- SSPRK3 execution;
- Float arithmetic;
- integral diagnostics;
- optional final-state dump.

Formal refinement currently connects the executable kernel instantiated over `Real` to the mathematical schemes.
There is not yet a proof that the machine `Float` run lies within a certified error bound of the exact-real run.

## Verification infrastructure

The repository currently uses:

- frozen specifications/result maps;
- trusted statement modules;
- bridge theorems;
- `KernelAudit.lean`;
- verifier fixtures and `scripts/verify.py`;
- raw-type/evidence pinning;
- `lake comparator --paranoid` challenge checking;
- theorem catalog generation and coverage checks.

## Paper integration

JST paper material has been folded into `CFDLean/Papers/JST1/`. The catalog contains the current paper theorem set,
with some proofs delegated to the generic numerical core. Remaining paper gaps and acceptance status are tracked in
the roadmap and review records.

Status (2026-11-26, status `candidate`): 115 frozen paper-1 statements, all proved with standard axioms
(`specifications/JST1/P1.md` .. `P6.md`; 37 delegate to MC-N). P4: `prop:wallJST`, `prop:consistency`(b),(c),
`prop:sstpde`, `lem:sstentropy` Hessian. P5: the Ismail-Roe flux is smooth near the diagonal and `F^IR - mean =
O(|y||Δu|²)` (gap G6, Lean side), and bridge theorems from the paper's Euler definitions to M1 (differences in
`P5.md`). P6: `∫_T φ_i = m_T` with the Lebesgue integral, `|T| = |det|/d!`, and the Galerkin form of
`prop:consistency`(b). Not covered: mixed cells that are not affine images of the reference cells (trilinear
hexahedra). Paper gaps for the paper session: `specifications/JST1/PAPER_GAPS.md` (G5-G7 open, P6 notes).

## Current architectural limitation / next stress test

The Burgers line is still a periodic, uniform-cell, cell-centered FV specialization. The next recommended geometry
stress test is a non-uniform fixed 1D mesh with explicit cell geometry and geometry-aware MUSCL reconstruction.

See:

- `roadmap/NEXT.md` for actionable work;
- `roadmap/FUTURE.md` for longer-horizon CFD goals;
- `roadmap/PRINCIPLES.md` for design rules that should remain stable.
