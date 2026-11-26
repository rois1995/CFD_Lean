# Roadmap: long-lived design principles

These are the architectural objectives that should survive individual milestones. They are not a promise that every
feature exists today. Changing one of these principles should be an explicit design decision, not an incidental
consequence of implementing a new scheme.

## 1. The trusted object is the formal statement and checked proof

The intended trust chain is:

```text
scientific source / modelling decision
        ->
reviewed formal statement
        ->
Lean proof
        ->
kernel / comparator checking
        ->
executable refinement
        ->
run provenance
```

Agents, generated code, numerical experiments and external implementations can propose evidence, but they are not the
source of mathematical truth.

## 2. Separate PDE semantics, discretization, execution and machine arithmetic

Do not prove CFD mathematics directly against CUDA, MPI, mutable arrays or a compiler backend.

Keep explicit refinement layers:

```text
physical model
  -> mathematical discretization
  -> executable algorithm
  -> machine arithmetic
  -> optimized / parallel backend
```

Each arrow should have its own specification and proof obligations.

## 3. Be discretization-agnostic at the right level

The library should support different realizations of the same numerical ideas without pretending that their geometry
is identical.

Examples already present are:

- cell-centered periodic finite volume for the scalar Burgers line;
- node-centered median-dual control volumes for the Euler line.

Flux consistency, conservation, entropy concepts and time composition should be shared where mathematically natural.
Reconstruction, geometry, boundary assembly and other method-specific operators should remain specialized.

## 4. Keep mesh and field conceptually distinct

New generic APIs should not require one global `dx`, an eternally fixed index set, or immutable geometry.

The architecture should remain compatible with a future dependent state such as

```text
(mesh, values : mesh.Dof -> U)
```

even while simple milestones continue to use `Fin n -> U`.

This is required for non-uniform grids, ALE motion, remeshing and AMR.

## 5. Geometry is data with explicit validity assumptions

Numerical theorems should state the geometric hypotheses they need: positive volumes, valid orientation, conforming
connectivity, admissible face measures, and so on.

Mesh-quality heuristics need not all be formally optimal, but invalid geometry must never be silently accepted as if
it satisfied a theorem's hypotheses.

## 6. Physical boundary conditions and discrete boundary realizations are different layers

A physical boundary condition should have method-independent semantics where possible. Its numerical realization may
be different for:

- cell-centered FV (exterior / ghost states and face fluxes);
- node-centered dual FV (boundary patches / transfers);
- FEM or DG (weak boundary terms).

Prove that each discrete realization implements the intended physical condition rather than forcing one universal
discrete BC mechanism.

## 7. Certificates should remain composable

Prefer separate properties such as:

- consistency;
- conservation;
- monotonicity;
- Lipschitz bounds;
- TVD / invariant-region preservation;
- entropy stability;
- positivity / admissibility;
- constant-state preservation;
- geometric conservation;
- conservative remapping.

Avoid monolithic scheme structures that make reuse or replacement of one component unnecessarily difficult.

## 8. Conservation and admissibility are first-class global invariants

For realistic systems, the framework should make it possible to track appropriate invariants across:

- spatial discretization;
- time integration;
- boundary conditions;
- mesh motion;
- remapping;
- checkpoint / restart;
- parallel execution.

For compressible flow, positivity of density and pressure and preservation of the admissible state set should become
first-class proof obligations where the chosen method supports them.

## 9. Reconstruction and gradients are geometry-aware components

Do not hard-code uniform-grid formulas such as `+/- slope/2` into the generic reconstruction concept.

Uniform MUSCL should be a specialization of a geometry-aware reconstruction. Higher-dimensional gradient
reconstruction and viscous operators should fit the same component/certificate philosophy.

## 10. Time evolution is more general than one fixed explicit step

Generic APIs should leave room for:

- variable time steps and CFL policies;
- SSP methods;
- implicit and IMEX methods;
- pseudo-time / steady iterations;
- nonlinear and linear solver tolerances;
- residual-based stopping criteria.

The current explicit schemes are concrete realizations, not the universal definition of time evolution.

## 11. Exact-real, floating-point and optimized results are different claims

Keep these claims separate:

```text
exact mathematical theorem
exact-algorithm refinement
floating-point error / enclosure
parallel or optimized implementation refinement
```

A `Float` run must not inherit exact-real guarantees without a proved machine-arithmetic bridge.

## 12. Maintain a strong reference mode even if faster modes are added

A future solver may deliberately offer two styles:

- a deterministic reference mode with the strongest reproducibility and proof coverage;
- performance modes using GPU/MPI, fused kernels and less constrained reduction order, with appropriate bounded-error
  or refinement guarantees.

The reference implementation can be valuable as a formally grounded comparator even if it is not the fastest CFD
code.

## 13. Parallelism and repartitioning live below numerical semantics

Domain decomposition, ownership, halos, overlap schedules, GPU thread mappings and MPI repartitioning should refine
the same global mathematical operator.

A repartition changes ownership, not the mathematical mesh. AMR/remeshing changes the approximation space and
therefore requires a numerical transfer operator. Do not conflate the two.

## 14. A formally meaningful run needs provenance

The long-term output of the project is not just an array of numbers. A reference run should be able to identify:

- repository commit and formal specification version;
- mesh and initial/boundary data hashes;
- physical model;
- reconstruction / flux / time integrator;
- timestep policy;
- arithmetic and execution backend;
- applicable theorem/certificate set;
- deterministic/reproducibility settings.

A machine-readable run/guarantee manifest should eventually travel with output data.

## 15. Distinguish implementation, discretization and modelling error

The long-term verification story should keep separate:

- implementation/refinement error;
- machine-rounding error;
- discretization error;
- modelling error.

Proving that code implements a scheme is not by itself a convergence or physical-validity theorem.

## 16. Stress-test abstractions with concrete milestones

Do not generalize merely because a future feature can be imagined. Introduce abstractions when a concrete milestone
needs them, while ensuring current APIs do not unnecessarily rule out known future requirements.

The first planned stress test for the present scalar FV abstractions is a non-uniform fixed 1D mesh.


## 17. New equation systems enter through capabilities, not solver clones

Adding a new PDE family should primarily extend the physical-model layer with the capabilities that actually exist for
that model, for example:

- state and admissibility;
- convective flux;
- entropy structure;
- wave-speed or spectral information;
- diffusive / viscous constitutive laws;
- source terms;
- constraints.

Generic numerical components should depend only on the capabilities they need. Burgers, Euler, Navier-Stokes,
multispecies flow and future systems should reuse common discretization/time/execution machinery where the mathematics
is genuinely shared.

Do not force every PDE into one universal conservation-law interface. Constrained systems such as incompressible flow
may require a different solver structure while still reusing geometry, gradients, time integration, linear solvers and
execution refinement.

## 18. Arithmetic precision belongs to the execution backend

Keep generic `Physics`, `Geometry`, `Discrete`, `Schemes`, `Entropy`, and `Time` mathematics independent of machine
types such as `Float` and `Float32`. Preserve arithmetic polymorphism in executable kernels where practical. Select
precision in execution and refinement layers. If the algorithm itself depends on a representation, state that
dependence explicitly in its specification.

Keep the path to a certified run explicit.

```text
mathematical scheme over ℝ
  -> generic numerical kernel with exact-real refinement
  -> selected arithmetic backend
  -> backend-specific refinement or error certificate
  -> certified run under the certificate's hypotheses
```

The kernel interpreted over `ℝ`, binary32 and binary64 implementations, arbitrary precision, interval enclosures,
and mixed precision are distinct realizations with distinct proof obligations. Extending an exact-real guarantee to
a machine run requires a theorem relating the selected backend to the exact algorithm under stated hypotheses.
An optimized or parallel implementation has its own refinement obligations, including any change in reduction order.
