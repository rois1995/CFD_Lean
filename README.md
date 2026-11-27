# CFD_Lean

CFD_Lean is a Lean 4 library of exact-real contracts and proofs for computational fluid dynamics. It
formalizes numerical methods and connects the periodic 1D Burgers schemes to an executable array kernel.

| Area | Current coverage |
|---|---|
| Euler and Roe | Ideal-gas Euler states and fluxes, Roe linearization and flux, median-dual assembly and boundary transfers. M1–M4 are independently accepted. The M5 lumped explicit Euler update awaits independent acceptance. |
| Burgers | Periodic uniform-grid Rusanov, Forward Euler and SSP Runge–Kutta, MUSCL limiters, semidiscrete entropy stability, and exact-real array refinement. B0–B4, B3b and E0–E0c await independent acceptance. |
| JST paper | Formal statements and proofs for paper 1, with shared simplex, mesh and pair-flux results in the numerical core. |

## Build and run

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root. Lake uses the
[Lean toolchain](lean-toolchain) and [dependency pins](lake-manifest.json) recorded in the clone.

```bash
lake build
lake exe burgers1d 200 200 0.4
lake exe burgers1d 200 600 0.12 --limiter vanleer
lake exe fv1d --model burgers 200 600 0.12 --limiter vanleer
lake exe fv1d --model euler 4 --dump
```

The Burgers arguments are cell count, step count and CFL number. Add `--dump` for the final cell values.
`--muscl` selects unlimited reconstruction, which can overshoot. Use `--limiter minmod` for the
former E0b behavior. See the [driver and kernel guide](CFDLean/Exec/README.md) for limiter choices, explicit cell widths and the first-order Euler density-wave comparison.

`burgers1d` runs the kernel with `Float`. The refinement theorems apply to the kernel instantiated
with `ℝ`. The driver, compiler and floating-point error are outside that proof boundary.

## Find your way around

- [Architecture](ARCHITECTURE.md) and [concept-to-code map](docs/CONCEPTS.md) show where definitions and proofs live.
- [Theorem catalog](catalog/README.md) indexes promised results. [Specifications](specifications/) and
  [review records](reviews/) give their frozen scope and independent acceptance status.
- [Contributor guide](CONTRIBUTING.md) and [agent guide](AGENTS.md) explain the PR, milestone and verification workflow.
- [Current status](roadmap/CURRENT.md) and [next steps](roadmap/NEXT.md) track the work. [TODO.md](TODO.md) indexes the roadmap.
- [Euler and Roe checkpoints](references/Euler-Milestones.md) preserve the historical M1 replay and acceptance details.
  [Burgers B0](references/Burgers-B0.md), [B3b](references/Burgers-B3b.md), and [E0c](references/Burgers-E0c.md)
  are entry points into the Burgers contracts and proof maps. [JST1 specifications](specifications/JST1/README.md)
  map the paper statements to their implementations.
