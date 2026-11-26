# CFD_Lean roadmap index

Status date: 2026-11-26.

This file is intentionally short. It answers four questions:

1. **Where is the project now?** -> [roadmap/CURRENT.md](roadmap/CURRENT.md)
2. **What should we work on next?** -> [roadmap/NEXT.md](roadmap/NEXT.md)
3. **Where might the project go later?** -> [roadmap/FUTURE.md](roadmap/FUTURE.md)
4. **Which architectural rules should remain stable?** -> [roadmap/PRINCIPLES.md](roadmap/PRINCIPLES.md)
5. **When should future architecture actually be implemented?** -> [roadmap/SEQUENCING.md](roadmap/SEQUENCING.md)

## Immediate orientation

The project already contains:

- an independently accepted Euler/Roe/median-dual line through M4, with M5 implemented;
- a Burgers line through B4;
- executable first-order and MUSCL array kernels with exact-real refinement proofs;
- a native `burgers1d` executable using `Float`;
- theorem cataloguing, trusted statement bridges, kernel audit and comparator-based checking;
- integrated JST paper formalization.

The main near-term concerns are no longer simply "add another scheme". They are:

1. close the scientific/review backlog on the implemented Burgers milestones;
2. align Burgers and Euler on one uniform periodic 1D solver, and use non-uniform cells as the next geometry test;
3. choose a credible machine-arithmetic verification strategy for E1;
4. begin run provenance/output infrastructure suitable for future formally grounded reference simulations;
5. continue M6 and selected mathematical extensions without breaking the long-term architecture.

## Roadmap documents

### [CURRENT.md](roadmap/CURRENT.md)

Concise factual snapshot of what is already implemented, merged, accepted, pending and executable.

Use this first when asking "what does CFD_Lean actually do today?"

### [NEXT.md](roadmap/NEXT.md)

Actionable near-term work, ordered by priority.

This is the working TODO list. Items should move here only when they are concrete enough to scope as a proposal,
milestone or engineering task.

### [FUTURE.md](roadmap/FUTURE.md)

Long-horizon technical directions that should influence architecture but are not immediate implementation commitments.

It includes:

- non-uniform and general control-volume geometry;
- BC architecture;
- ALE and moving meshes;
- conservative remapping and AMR;
- positivity/admissibility;
- viscous terms and Navier-Stokes;
- higher-order reconstruction;
- variable/implicit time integration;
- residual semantics;
- multiphysics;
- CPU/GPU/MPI execution;
- deterministic reference mode;
- canonical benchmarks and manufactured solutions;
- convergence/error decomposition;
- verified output manifests;
- correspondence with external CFD codes.

### [SEQUENCING.md](roadmap/SEQUENCING.md)

Implementation triggers and prerequisite ordering for architectural choices. It distinguishes what should influence
design now from what should wait for a concrete milestone, and records which capabilities ought to precede ALE, AMR,
Navier-Stokes, implicit solvers, GPU/MPI, multiphysics and other long-horizon work.

### [PRINCIPLES.md](roadmap/PRINCIPLES.md)

Long-lived design constraints: the "stone-carved objectives".

Among them:

- trusted statements and checked proofs define the mathematical claim;
- separate physical model, discretization, executable algorithm and machine arithmetic;
- be discretization-agnostic only where mathematically justified;
- keep mesh and field conceptually distinct;
- keep geometry and BC assumptions explicit;
- favor composable certificates;
- treat conservation/admissibility as first-class invariants;
- keep reconstruction and gradients geometry-aware;
- do not hard-wire generic time evolution to one fixed explicit step;
- never silently transfer exact-real guarantees to `Float`;
- keep repartitioning separate from remeshing;
- make future verified runs carry provenance and theorem coverage.

## Detailed project records

This roadmap does not replace the authoritative project artifacts:

- `specifications/` -- frozen contracts, approvals, result maps and accepted pins;
- `references/` -- source/result traceability and milestone explanations;
- `reviews/` -- independent review and acceptance records;
- `catalog/` -- theorem catalog and classification;
- `evidence/` -- generated verification/audit evidence;
- `Challenges/` -- comparator challenges;
- `scripts/` -- verifier, replay and catalog tooling.

When roadmap prose and a frozen contract disagree, the frozen contract/review record is authoritative for that
milestone.

## Maintenance rule

Keep this index short.

- Update `CURRENT.md` when project status materially changes.
- Update `NEXT.md` when priorities or concrete milestones change.
- Check off completed roadmap items in the PR that completes them. [Contributor guide](CONTRIBUTING.md)
- Move speculative items to `FUTURE.md`.
- Update `SEQUENCING.md` when concrete experience changes implementation prerequisites or trigger conditions.
- Change `PRINCIPLES.md` only for deliberate architectural decisions.
- Do not turn `TODO.md` back into a chronological implementation log.
