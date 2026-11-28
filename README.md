# CFD_Lean

CFD_Lean is a Lean 4 library of exact-real contracts and proofs for computational fluid dynamics. It
formalizes numerical methods and connects the periodic 1D Burgers schemes to an executable array kernel.

## Repository capabilities

CFD_Lean includes periodic Burgers and Euler finite-volume infrastructure, nonuniform 1D geometry,
reconstruction and executable refinement, and the median-dual Euler/Roe line. The
[capability map](docs/CAPABILITIES.md) records evidence and status for each scope. The
[architecture graph](docs/ARCHITECTURE-GRAPH.md) follows actual Lean imports. Start with the
[documentation home](docs/index.md) for the building blocks and contributor guides.

## Build and run

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root. Lake uses the
[Lean toolchain](lean-toolchain) and [dependency pins](lake-manifest.json) recorded in the clone.

```bash
lake build
lake exe fv1d --model burgers 200 200 0.4
lake exe fv1d --model burgers 200 600 0.12 --limiter vanleer
lake exe fv1d --model euler 4 --dump
```

The Burgers arguments are cell count, step count and CFL number. Add `--dump` for the final cell values.
`--muscl` selects unlimited reconstruction, which can overshoot. Use `--limiter minmod` for the
former E0b behavior. See the [driver and kernel guide](CFDLean/Exec/README.md) for limiter choices, explicit cell widths and the first-order Euler density-wave comparison.

To migrate a Burgers run, replace `lake exe burgers1d` with `lake exe fv1d --model burgers` and keep the remaining arguments.

`fv1d` runs the kernel with `Float`. The refinement theorems apply to the kernel instantiated
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
