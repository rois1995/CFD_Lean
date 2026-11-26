# Roadmap: future goals

This file records directions that should influence architecture now but are not immediate implementation commitments.
Concrete work should move to `NEXT.md` only when a proposal has a clear scope and proof boundary.

## 1. Verified CFD output as an end-to-end object

The long-term goal is not merely "proofs about CFD formulas". It is a solver whose output can be traced through:

```text
physical model
  -> discrete scheme
  -> mathematical guarantees
  -> executable algorithm
  -> machine arithmetic
  -> parallel / optimized backend
  -> output artifact + provenance
```

A useful success case is a formally grounded reference solution that can be compared against SU2, OpenFOAM,
research codes or optimized variants of CFD_Lean itself.

## 2. Fixed-mesh geometry beyond uniform periodic 1D

After the non-uniform 1D stress test:

- develop a general oriented control-volume interface exposing degree of freedom, volume/measure, neighbours and
  oriented interfaces;
- connect cell-centered and node-centered dual-CV realizations through common flux/conservation/entropy concepts;
- retain method-specific reconstruction and geometry;
- generalize to higher-dimensional unstructured meshes where concrete use cases justify it.

## 3. Boundary-condition framework

Develop physical BC semantics and certified method-specific realizations for cases such as:

- periodic;
- prescribed/inflow states;
- symmetry;
- slip walls;
- no-slip walls;
- adiabatic/isothermal walls;
- subsonic/supersonic inflow and outflow;
- characteristic or non-reflecting conditions.

Boundary correctness should be part of the theorem boundary of realistic test cases, not an unverified afterthought.

## 4. ALE and moving meshes

Once fixed control-volume geometry is mature:

1. make mesh motion explicit;
2. define ALE fluxes using face/grid velocity;
3. prove a discrete geometric conservation law;
4. prove constant-state preservation under admissible mesh motion;
5. keep mesh-motion laws separate from the physical PDE.

Do not begin full ALE by mutating the current uniform Burgers kernel in place.

## 5. Conservative mesh-to-mesh remapping

Before full AMR, introduce an explicit transfer

```text
Remap oldMesh newMesh oldState -> newState
```

and separate certificates such as:

- conservation of primary conserved quantities;
- constant preservation;
- positivity/admissibility;
- bounds / invariant-region preservation;
- entropy behavior where meaningful.

For finite-volume high-order methods, prefer remapping the conservative primary state and reconstructing higher-order
data again on the new mesh unless a stronger transfer is specifically justified.

## 6. Refinement, coarsening and AMR

Model adaptation as certified mesh transformations with local parent/child relationships and valid resulting geometry.

The refinement indicator may be heuristic. The formal obligations are that:

- the new mesh satisfies required validity/conformity properties;
- the state transfer satisfies its certificates;
- the resumed numerical operator is well-defined on the new mesh.

Later combine this with load balancing while keeping numerical remeshing distinct from execution repartitioning.

## 7. Positivity and admissibility for compressible flow

For Euler/Navier-Stokes development, prioritize preservation of physically admissible states, including positive
density and pressure.

Potential components:

- invariant-domain or positivity-preserving fluxes;
- positivity-preserving reconstruction/limiting;
- timestep restrictions;
- certified fallback/limiting strategies.

## 8. Viscous terms, gradients and Navier-Stokes

A production CFD line will need reusable components for:

- gradient reconstruction;
- Green-Gauss / least-squares style gradient operators;
- skew/non-orthogonal corrections;
- viscous flux construction;
- diffusion consistency and stability;
- wall-gradient / thermal boundary treatment.

Treat gradient reconstruction as its own geometry-aware certified component rather than baking it into one scheme.

## 9. Higher-order spatial methods

Beyond MUSCL/minmod, possible milestones include:

- additional TVD limiters;
- higher-order polynomial reconstruction;
- WENO-family methods;
- multidimensional limiting;
- DG or related high-order formulations where they fit the project.

The reusable object should be a reconstruction/projection component plus certificates, not a hard-coded named solver.

## 10. Variable timestep and adaptive time integration

Realistic runs need local/global wave-speed based timestep selection and possibly variable `dt`.

Future proof obligations include:

- correctness of a CFL estimator;
- preservation of invariants under a sequence of varying timesteps;
- SSP properties under variable step restrictions;
- event/output scheduling independent of step count.

## 11. Implicit, steady and multigrid solvers

Do not restrict the project forever to explicit stepping.

Potential future layers:

- pseudo-time continuation;
- Newton / nonlinear iteration;
- Krylov solvers;
- preconditioners;
- multigrid;
- implicit or IMEX time integration;
- certified residual and stopping criteria.

The algebraic solver should refine the intended discrete equation to a stated tolerance rather than silently replacing
it with an implementation-specific notion of convergence.

## 12. Residual semantics and stopping criteria

For steady or implicit problems, distinguish:

- discrete equation residual;
- physical conservation imbalance;
- norm/scaling used for monitoring;
- stopping tolerance;
- any theorem connecting residual magnitude to solution error.

"Residual converged" should eventually have a machine-checkable meaning.

## 13. State extensibility and multiphysics

Keep generic numerical interfaces capable of states beyond scalar Burgers or the fixed five-variable Euler state, for
example:

- passive scalars;
- multispecies flow;
- turbulence variables;
- MHD;
- level-set or interface variables.

Avoid unnecessary assumptions about memory layout in the mathematical layer.

## 14. Parallel CPU, GPU and distributed memory

Planned execution refinement stages include:

1. parallel CPU;
2. GPU kernels;
3. optimized/fused/tiled GPU kernels;
4. multi-GPU / MPI;
5. CUDA-aware MPI or equivalent device-aware communication.

Core proof concepts:

- partition completeness/disjointness;
- valid halo states;
- local stencil = global stencil on owned cells;
- communication re-establishes halo validity;
- reduction semantics;
- deterministic reference reductions versus bounded non-deterministic floating-point reductions.

## 15. Reference mode versus performance mode

Maintain a path to a deterministic reference execution with the strongest proof and reproducibility guarantees.

Optimized modes may use different scheduling, reduction order and fusion. They should come with an explicit refinement
or numerical-error contract rather than being treated as bitwise equivalent by assumption.

## 16. Canonical verification and validation cases

Create machine-readable specifications for progressively richer benchmarks, for example:

- Burgers shock/rarefaction problems;
- Sod and Lax shock tubes;
- Shu-Osher;
- isentropic vortex;
- manufactured solutions;
- Taylor-Green vortex;
- later viscous wall-bounded cases.

The goal is to make the problem statement itself unambiguous: domain, mesh, initial state, BCs, parameters, numerical
method and expected theorem coverage.

## 17. Manufactured solutions

Manufactured solutions are especially attractive for the formal framework:

```text
analytic field
  -> proved forced PDE identity
  -> exact boundary/initial data
  -> numerical convergence experiment
```

This can separate implementation correctness from discretization accuracy and provide rigorous regression cases.

## 18. Accuracy, convergence and error decomposition

Long-term results should distinguish:

- implementation/refinement correctness;
- floating-point error;
- discretization error;
- modelling error.

Possible future work includes formal order-of-accuracy statements, convergence to entropy/weak solutions where
tractable, and a posteriori error bounds for selected schemes.

## 19. Output artifacts and guarantee manifests

A future reference result may be packaged conceptually as:

```text
result/
  solution.*
  mesh.*
  run.json
  theorem-manifest.json
  hashes.txt
```

The theorem manifest should say which guarantees apply and under which checked hypotheses. The exact file formats are
a later engineering decision; the provenance model should be designed before many incompatible output formats exist.

## 20. Correspondence with external CFD codes

Potential high-value verification targets include:

- formally relating a CFD_Lean scheme to an implementation in SU2 or another code;
- using CFD_Lean reference runs as regression/comparison oracles;
- proving optimized backends refine a common scheme;
- comparing formally stated benchmark setups rather than only output plots.

This can make the project scientifically useful even before it becomes a full-scale production CFD package.


## 21. Extensible PDE and physical-model architecture

New equation sets should be folded into the framework primarily through composable physical capabilities rather than
by cloning an entire solver stack.

A useful conceptual decomposition is:

```text
Physical model
  state
  admissibility
  convective flux              optional
  diffusive / viscous flux     optional
  source term                  optional
  entropy structure            optional
  wave-speed / spectral data   optional
  constraints                  optional
```

Examples:

- Burgers: scalar state + convective flux;
- Euler: system state + admissibility + convective flux + entropy/spectral structure;
- Navier-Stokes: Euler convective physics + viscous constitutive model + gradients;
- multispecies flow: compressible flow + species transport + coupling/source terms;
- RANS: Navier-Stokes + turbulence transport/source models;
- incompressible flow: evolution + divergence constraint + pressure/projection machinery rather than a forced
  hyperbolic-conservation-law abstraction.

Implementation timing and prerequisites are tracked in `SEQUENCING.md`. The intended rule is to prepare interfaces
now by avoiding equation-name-specific generic APIs, but wait for a third concrete equation family or a genuine
convective+viscous/source composition need before introducing broad new Physics capability abstractions.
