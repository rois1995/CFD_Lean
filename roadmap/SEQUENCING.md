# Roadmap: sequencing and implementation triggers

Status date: 2026-11-26.

This file answers a different question from `NEXT.md` and `FUTURE.md`:

> **When should an architectural idea become actual implementation work?**

The purpose is to avoid both extremes:

- implementing speculative abstractions before a concrete use case exposes the right interface;
- discovering too late that earlier APIs hard-coded assumptions that block an important future direction.

The categories below are:

- **Prepare now** -- constraints or documentation that should influence current work.
- **Start implementation when** -- a concrete trigger that justifies writing Lean/code.
- **Should precede** -- later features that benefit from this being settled first.
- **Do not require first** -- work that can proceed independently and should not be blocked unnecessarily.

These are sequencing guidelines, not a single serial project plan. Independent branches of work may proceed in parallel.
The [current scheduling decision](NEXT.md#next-decision-after-the-unified-1d-driver) identifies the next deliverable
and the prerequisites for the E1 and fixed-mesh 2D work.

## Summary dependency spine

The main architectural spine currently envisioned is:

```text
navigation / architecture documentation
        |
        v
non-uniform fixed 1D FV
        |
        v
general fixed control-volume geometry
        | \
        |  \--> geometry-aware multidimensional reconstruction / gradients
        |             |
        |             v
        |        viscous terms / Navier-Stokes
        |
        +--> mesh-dependent state
                |
                +--> ALE / moving mesh
                |
                +--> conservative remap
                         |
                         v
                  refinement/coarsening
                         |
                         v
                        AMR
```

A separate execution spine is:

```text
exact mathematical scheme
        |
        v
array/executable refinement
        |
        +--> machine-arithmetic model / E1
        |
        +--> provenance + deterministic reference output
        |
        v
parallel CPU
        |
        v
GPU / MPI / optimized execution
```

And a physics/model spine is:

```text
Burgers + 1D Euler on the same periodic FV step
        |
        v
additional physical-model capabilities as needed
        |
        +--> additional hyperbolic systems
        |
        +--> source terms / multiphysics
        |
        +--> diffusive/viscous models
        |
        +--> constrained systems with their own solver structure
```

## 1. Repository navigation and architectural documentation

**Prepare now:** already authorized as immediate work package A.

**Start implementation when:** immediately; this is documentation-only.

**Should precede:** larger structural refactors, because agents and humans need a common description of intended layer
boundaries before changing them.

**Do not require first:** review backlog, new mathematics, E1 design.

Generated/code-backed navigation tooling (work package B) should follow the documentation layer and receive the normal
build/verifier checks.

## 2. Review and acceptance backlog

**Prepare now:** no special architecture is needed; keep accepted/pending/candidate status explicit.

**Start implementation when:** immediately.

**Should precede:** accumulation of many more theorem-bearing milestones whose scientific statements have not received
independent review.

**Do not require first:** documentation-only navigation work or exploratory design proposals.

The objective is to keep implementation velocity from outrunning the trust/acceptance process indefinitely.

## 3. Non-uniform fixed 1D finite volume

**Prepare now:** avoid adding new generic assumptions of one global `dx`; keep geometry separate from field values.

**Start implementation when:** after the navigation/documentation pass, as the next concrete geometry stress test.

**Should precede:**

- a general control-volume geometry abstraction;
- full geometry-aware multidimensional reconstruction;
- ALE/AMR abstractions that would otherwise be designed without a simpler non-uniform test case.

**Do not require first:**

- floating-point verification;
- GPU/MPI;
- Navier-Stokes;
- general unstructured mesh support.

The purpose of this milestone is partly scientific and partly architectural: learn which current Burgers abstractions
actually need generalization.

## 4. General fixed control-volume geometry

**Prepare now:** maintain the distinction between cell-centered primal CVs and node-centered median-dual CVs.

**Start implementation when:** the non-uniform 1D milestone has identified the minimum geometry information required
by conservation, reconstruction and CFL/stability statements, and there is at least one second concrete geometry
(the existing median-dual line already provides one).

**Should precede:**

- a generic ALE formulation;
- general conservative remapping;
- multidimensional FV reconstruction;
- serious unstructured-mesh executable work.

**Do not require first:** a universal mesh library or support for every cell type.

Do not design this as "the most general mesh imaginable"; design the smallest interface that cleanly instantiates the
concrete discretizations already present.

## 5. Extensible PDE / physical-model capability architecture

**Prepare now:**

- keep physical models in the Physics layer;
- avoid generic numerical APIs that pattern-match on a concrete equation name;
- treat physical flux, admissibility, entropy, wave-speed information, viscous fluxes, sources and constraints as
  separable capabilities where mathematically appropriate.

**First shared solver:** the uniform 1D Burgers and Euler proposal exercises the same numerical method with two
state types. Extract the operations that both first-order steps need when that proposal is frozen. Non-uniform
meshes and multidimensional Roe assembly can progress independently. [1D work package](NEXT.md#priority-1---shared-1d-finite-volume-for-burgers-and-euler)

**Extend those capabilities when:** one of these triggers occurs:

1. a third genuinely distinct equation set is added (for example shallow water or MHD);
2. Navier-Stokes requires composing Euler convective physics with a viscous constitutive model;
3. a source-driven/multiphysics system requires a reusable source-term interface.

At that point there is enough evidence to design interfaces from multiple real examples instead of guessing.

**Should precede:**

- broad multiphysics support;
- many equation-specific solver clones;
- generic benchmark/configuration machinery that needs to describe multiple physical models.

**Do not require first:** non-uniform geometry, E1, ALE, GPU/MPI.

Do **not** force constrained systems such as incompressible flow into a fake conservation-law interface. Reuse
capabilities where they are mathematically shared and allow different solver structures where they are not.

## 6. Boundary-condition framework

**Prepare now:** keep physical BC semantics distinct from their discrete realization.

**Start implementation when:** before the first substantial non-periodic benchmark or before a new method needs a
second realization of the same physical BC. A good trigger would be a verified Euler shock-tube/wall/outflow suite or
a multidimensional benchmark with physical boundaries.

**Should precede:**

- realistic external/internal-flow reference cases;
- Navier-Stokes wall treatment;
- manufactured-solution infrastructure intended to exercise boundaries.

**Do not require first:** ALE, AMR, floating-point verification.

A small set of concrete BCs should drive the abstraction; do not attempt to enumerate every CFD boundary condition up
front.

## 7. Positivity / admissibility framework

**Prepare now:** continue treating admissibility predicates as Physics-level objects and avoid numerical APIs that
assume arbitrary states are always valid.

**Start implementation when:** the Euler line reaches a concrete multi-step/high-order executable path where loss of
positive density or pressure is a practical concern, or before claiming robust compressible reference simulations.

**Should precede:**

- aggressive high-order compressible schemes;
- serious Navier-Stokes reference cases;
- adaptive/remapped compressible simulations where transfer can violate admissibility.

**Do not require first:** scalar Burgers extensions.

## 8. Geometry-aware multidimensional gradients and reconstruction

**Prepare now:** keep reconstruction as a replaceable component and do not generalize 1D MUSCL by hard-coded
coordinate assumptions.

**Start implementation when:** either:

- a two-/three-dimensional MUSCL-style FV milestone is selected; or
- Navier-Stokes requires gradients for viscous fluxes.

**Should precede:** viscous Navier-Stokes and higher-dimensional high-order FV.

**Do not require first:** ALE or AMR.

The first implementation should be driven by a concrete geometry and method (for example Green-Gauss or
least-squares), with generic certificates extracted only after common structure is visible.

## 9. Viscous terms and Navier-Stokes

**Prepare now:** preserve Euler as a reusable convective model and leave room for diffusive/viscous physical
capabilities.

**Start implementation when:**

- multidimensional geometry and gradient reconstruction have a stable interface;
- the necessary wall/thermal BC semantics are available for the intended test case;
- there is a concrete Navier-Stokes milestone/benchmark rather than a purely abstract desire for viscosity.

**Should precede:** serious viscous benchmark suites, RANS, many turbulence models.

**Do not require first:** ALE/AMR, GPU/MPI, a complete implicit-solver stack. An explicit first Navier-Stokes
milestone is acceptable if its timestep restrictions are clearly stated.

## 10. Variable timestep / CFL policy

**Prepare now:** do not define generic evolution as repeated application of one eternally fixed `dt`.

**Start implementation when:** the first realistic reference run would materially benefit from recomputing the stable
timestep from the evolving state, or before variable-mesh/ALE runs where geometry changes the local timestep bound.

**Should precede:** practical long-running ALE/AMR simulations and many production-style reference cases.

**Do not require first:** implicit solvers.

The initial theorem target can be preservation of already-proved one-step invariants under a sequence of timesteps
that each satisfy their local hypotheses.

## 11. Implicit / steady / nonlinear / linear solver architecture

**Prepare now:** keep spatial residuals distinct from explicit timestep formulas and keep stopping criteria explicit.

**Start implementation when:** a selected problem makes explicit stepping impractical or when a steady/implicit
reference problem becomes an actual project milestone.

**Should precede:** claims about verified steady convergence, stiff multiphysics, production-like implicit
Navier-Stokes.

**Do not require first:** first Navier-Stokes mathematics, explicit benchmarks, ALE, AMR.

Do not build a generic Krylov/Newton hierarchy merely because production CFD codes have one; let a concrete discrete
problem determine the first solver contract.

## 12. Residual semantics and stopping criteria

**Prepare now:** keep diagnostic residuals distinguished from mathematical equation residuals.

**Start implementation when:** the first steady, nonlinear or inexact implicit solve is introduced.

**Should precede:** a user-facing claim that "the solver converged" has formal meaning.

**Do not require first:** explicit transient simulations.

## 13. E1 / machine arithmetic

**Prepare now.** Preserve the arithmetic-polymorphic kernel. Isolate `Float`-specific initialization, conversions,
I/O and diagnostics in the driver. Keep `Scalar` limited to operations the kernel needs and separate exact-real
refinement from machine-arithmetic claims. [E1 design scope](NEXT.md#priority-2---e1-machine-arithmetic-strategy)

**Start implementation when** E1 defines what a certified arithmetic backend means, or a concrete use case requires
another precision or backend. Any claim of certification must satisfy the corresponding backend contract.

**Should precede** formally certified binary32 or binary64 runs, arbitrary-precision reference execution, mixed-precision
GPU execution, and verified floating-point parallel reductions.

**Can proceed independently.** Exact-real development, non-uniform-grid mathematics, and other theorem work whose
statements do not depend on machine arithmetic.

## 14. Run provenance, output and deterministic reference mode

**Prepare now:** yes; the basic format can be designed early.

**Start implementation when:** immediately for lightweight provenance/snapshot support, before many incompatible
driver/output conventions accumulate.

**Should precede:**

- publication of reference datasets;
- checkpoint/restart workflows;
- comparisons with external CFD codes that aim to be reproducible;
- performance modes whose guarantees differ from reference mode.

**Do not require first:** E1. The manifest can accurately state that machine-arithmetic certification is absent.

## 15. Parallel CPU execution

**Prepare now:** keep partition/ownership semantics outside the mathematical PDE/scheme layer.

**Start implementation when:** the serial array kernel/refinement interface is stable enough that parallelism can be
proved as a refinement of an already-defined global operator, and there is a performance/use-case reason to do it.

**Should precede:** GPU/MPI proof architecture where the same partition/halo ideas will be reused.

**Do not require first:** full E1, although machine-arithmetic semantics must be considered for reductions.

## 16. GPU and MPI execution

**Prepare now:** keep execution semantics and numerical semantics separated; distinguish repartitioning from
remeshing.

**Start implementation when:**

- serial/parallel reference kernels have stable semantics;
- ownership/halo contracts exist;
- there is a real workload large enough to justify optimized execution.

For MPI, start once local-stencil/halo correctness is understood. For GPU, start once kernels have sufficiently stable
data layout and arithmetic contracts.

**Should precede:** multi-GPU production-scale experiments.

**Do not require first:** ALE/AMR, but dynamic adaptation will later add repartitioning complexity.

## 17. Mesh-dependent state model

**Prepare now:** avoid APIs that assume the index type can never change.

**Start implementation when:** a concrete feature requires states on two different meshes in the same theorem or
program -- conservative remapping is the clearest trigger. It may also become useful earlier for ALE if geometry
evolution makes the current representation awkward.

**Should precede:** general remapping and AMR.

**Do not require first:** non-uniform fixed meshes if they can be handled cleanly with a fixed index set.

This should not be introduced merely to replace simple `Fin n -> U` states with more dependent types everywhere.

## 18. ALE / moving meshes

**Prepare now:** ensure geometry is explicit and mutable/evolving mesh semantics are not ruled out.

**Start implementation when:**

- fixed non-uniform/control-volume geometry is stable;
- the state/geometry separation is clear;
- there is a specific ALE test case;
- the discrete geometric conservation law can be stated precisely.

**Should precede:** ALE + AMR combinations.

**Do not require first:** conservative remapping if topology remains fixed. ALE and remapping are related but distinct.

## 19. Conservative mesh-to-mesh remapping

**Prepare now:** conservation should already be phrased with control-volume measures where appropriate.

**Start implementation when:** two concrete meshes and a concrete transfer operation are needed, before full AMR.
A simple refinement/coarsening or mesh-motion remap test should drive the first interface.

**Should precede:** topology-changing AMR and restart-on-a-different-mesh workflows.

**Do not require first:** ALE with fixed topology.

## 20. Refinement / coarsening / AMR

**Prepare now:** distinguish numerical mesh change from execution repartitioning; keep mesh validity assumptions
explicit.

**Start implementation when:**

- mesh-dependent states are available;
- conservative remapping exists;
- mesh validity/refinement relations can be expressed;
- at least one fixed-mesh multidimensional solver is stable enough to benefit from adaptation.

**Should precede:** adaptive production/reference simulations and dynamic load balancing tied to AMR.

**Do not require first:** every sophisticated error estimator. The first adaptation indicator may be heuristic.

## 21. Canonical benchmarks

**Prepare now:** yes. Every new major capability should ideally be attached to a concrete benchmark/specification.

**Start implementation when:** immediately for simple cases; expand incrementally.

**Should precede:** claims that a new subsystem is usable for realistic CFD.

**Do not require first:** machine-arithmetic verification, provided the benchmark's theorem coverage is stated
accurately.

Examples can progress from Burgers and shock tubes to isentropic vortex, manufactured solutions, Taylor-Green and
viscous wall-bounded cases.

## 22. Manufactured solutions

**Prepare now:** keep source terms and BC semantics extensible.

**Start implementation when:** there is a source-term representation and a spatial discretization whose accuracy or
viscous behavior we want to test formally.

**Should precede:** strong order-of-accuracy validation for complex PDEs where closed-form homogeneous solutions are
scarce.

**Do not require first:** AMR, ALE, GPU/MPI.

## 23. Accuracy, convergence and error estimates

**Prepare now:** keep implementation error, machine error, discretization error and modelling error conceptually
separate.

**Start implementation when:** the corresponding discrete operator is stable enough that its consistency/order
statement will not immediately be invalidated by API churn. Start with small tractable cases rather than a universal
convergence theory.

**Should precede:** claims that a formally implemented scheme approximates a PDE solution to a quantified tolerance.

**Do not require first:** full production execution infrastructure.

## 24. Multiphysics, species, turbulence and other equation extensions

**Prepare now:** use the capability-oriented physical-model principle and avoid hard-coded state layouts in generic
mathematics.

**Start implementation when:** a specific scientifically motivated model is selected and its coupling structure can be
stated. Do not create generic multiphysics machinery before at least two concrete couplings expose common needs.

**Should precede:** broad configuration/plugin systems for arbitrary physics.

**Do not require first:** ALE/AMR or GPU/MPI unless the chosen application specifically needs them.

## Maintenance rule

When a future item becomes a concrete milestone:

1. check its **Start implementation when** trigger here;
2. move the actionable scope into `NEXT.md`;
3. write/freeze the appropriate specification before theorem-bearing implementation;
4. update this file if actual experience changes the dependency assumptions.

If a roadmap item is blocked, state the missing prerequisite explicitly rather than leaving it as an ambiguous
"future" task.
