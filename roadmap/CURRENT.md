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

## Shared periodic 1D finite volume

FV1D implements one exact-real Rusanov–Forward Euler step for Burgers and ideal-gas Euler on the same
uniform periodic grid. The four frozen results cover B0 agreement, M1 equal-state flux, constant states and
conservation of the three Euler quantities. [Independent implementation acceptance](../reviews/FV1D/Acceptance.md) covers all four results.
[Contract](../specifications/FV1D.md) · [Proof map](../references/FV1D.md)

FVN repeats the first-order and MUSCL steps on a fixed non-uniform periodic 1D mesh, with one width per cell and
rescaled MUSCL differences. It is implemented with eight frozen results, three exact controls and a trusted
challenge for the scalar claims. Independent implementation review is pending.
[Contract](../specifications/FV1D-nonuniform.md) · [Proof map](../references/FV1D-nonuniform.md)

FVNA adds executable array kernels with one width per cell (first order shared by Burgers and Euler; Burgers MUSCL
with every limiter and SSPRK2/SSPRK3) and proves that over the reals they compute the FVN steps. The four frozen
results cover the refinement, the uniform-width specialization and the transferred FVN guarantees, with exact controls
and a trusted challenge for FVNA-M and FVNA-T. The [independent review](../reviews/FVNA/Acceptance.md) accepted the implementation.
[Contract](../specifications/FV1D-nonuniform-array.md) · [Proof map](../references/FV1D-nonuniform-array.md)

## Burgers line

Merged into `main`:

- B0: composable scalar FV core, Rusanov consistency, conservation, constants;
- B1: monotonicity, TVD and bounds under CFL;
- B2: SSPRK2/SSPRK3 and multi-step stability/conservation;
- B3: MUSCL/minmod reconstruction with TVD/bounds and SSP composition;
- B3b: MUSCL unlimited by default (central slope) with a limiter factor on top; limiters minmod, MC, superbee,
  van Leer, van Albada with one certificate `SlopeBounded θ`; TVD/bounds for `θ ≤ 2` with Euler/SSPRK2/SSPRK3; an
  exact overshoot example for the unlimited scheme;
- B4: scalar entropy certificates and semidiscrete Burgers entropy stability;
- E0: executable first-order array kernel, real-arithmetic refinement, native `burgers1d`;
- E0b: executable MUSCL array kernel (minmod), refinement, and transferred B3 guarantees;
- E0c: executable MUSCL array kernel with a limiter choice (none, minmod, MC, superbee, van Leer, van Albada),
  refinement for every choice, transferred B3b guarantees (sum for all; bounds and TVD for every limiter).

All Burgers milestones above are implemented, merged and accepted at `4c77f6e` by the
[implementation review](../reviews/Burgers-Implementation/Review.md). Human review of the trusted Burgers statements
is still open.

## Executable status

`lake exe fv1d --model burgers` supports:

- first-order Rusanov;
- MUSCL + Rusanov, unlimited with `--muscl`, or with `--limiter none|minmod|mc|superbee|vanleer|vanalbada`;
- SSPRK3 execution;
- Float arithmetic;
- integral diagnostics;
- optional final-state dump.

The [model-selecting driver](../CFDLean/Exec/README.md#model-selecting-driver) also runs the first-order Euler density wave
to time 1/8. Both models accept explicit cell widths. The external reviewer
accepted the implementation at `f297eea`. [Driver acceptance](../reviews/FV1D/Driver_Acceptance.md)

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

Status (2026-11-27, status `candidate`): 121 frozen paper-1 statements, all proved with standard axioms
(`specifications/JST1/P1.md` .. `P8.md`; 37 delegate to MC-N). P4: `prop:wallJST`, `prop:consistency`(b),(c),
`prop:sstpde`, `lem:sstentropy` Hessian. P5: the Ismail-Roe flux is smooth near the diagonal and `F^IR - mean =
O(|y||Δu|²)` (gap G6, Lean side), and bridge theorems from the paper's Euler definitions to M1 (differences in
`P5.md`). P6: `∫_T φ_i = m_T` with the Lebesgue integral, `|T| = |det|/d!`, and the Galerkin form of
`prop:consistency`(b). P7: `lem:avg` for general hexahedra, prisms and pyramids whose pulling sub-tetrahedra keep
one orientation, and a twisted-cube counterexample without that hypothesis (paper gap G8). P8: a valid trilinear
hexahedron whose Kuhn split is not a triangulation, and a conforming 8-cell mesh of valid hexahedra whose interior
vertex 13 has `Σ_k n_13,k = (0, 0, 7/30) ≠ 0` (G8). Paper gaps for the paper session:
`specifications/JST1/PAPER_GAPS.md` (G1-G8 fixed in the paper on 2026-11-27; current reference
`/media/rausa/4TB/SU2_Versions/SU2_NewJST/Handbook/paper1/paper1.tex`; two P6 notes remain).

## Current architectural limitation / next stress test

The Burgers line is a periodic, cell-centered FV specialization. The non-uniform fixed 1D mesh with geometry-aware
MUSCL reconstruction (FVN) and its executable array kernels (FVNA) are implemented. FVNA has independent implementation acceptance.

See:

- `roadmap/NEXT.md` for actionable work;
- `roadmap/FUTURE.md` for longer-horizon CFD goals;
- `roadmap/PRINCIPLES.md` for design rules that should remain stable.
