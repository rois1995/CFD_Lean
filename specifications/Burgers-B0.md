# Burgers B0: composable exact-real finite-volume core

Status: **approved and frozen for implementation on 2026-11-25**.

This contract adds a scalar/Burgers development to CFD_Lean without changing the accepted Euler M1--M4 mathematical sources or expanding the claims of the current M5 implementation.

## Purpose

Add a new `CFDLean.Burgers` development that serves as the first reusable, composable numerical-scheme layer for scalar conservation laws.

The first target is the one-dimensional inviscid Burgers equation

[
u_t + left(rac{u^2}{2}ight)_x = 0
]

on a periodic uniform mesh, using exact real arithmetic.

The architectural objective is broader than one Burgers solver: new numerical methods are assembled from components whose mathematical contracts are already proved, so later PRs can inherit generic results instead of reproving them solver by solver.

## Frozen architectural decisions

1. **CFD_Lean is the core package.** No parallel core library is created.
2. **Burgers is isolated under `CFDLean.Burgers`.** Accepted Euler sources are not modified to force scalar abstractions into the Euler hierarchy.
3. **Properties are separate certificates.** A two-point numerical flux contains its evaluator; consistency and later properties such as monotonicity, entropy stability and Lipschitz bounds are separate predicates/theorems.
4. **A scalar conservation-law object is introduced in B0.** This gives the generic finite-volume layer an explicit physical-flux parameter while keeping Burgers as one instantiation.
5. **The mathematical periodic index is finite and cyclic.** The first implementation uses `ZMod N` with a nonzero-size hypothesis, unless the pinned Mathlib API makes a definitionally equivalent finite cyclic representation necessary for compilation.
6. **Conservation is proved first for the raw finite sum.** The constant-cell-width discrete integral follows as a corollary.
7. **External projects are interop targets, not core dependencies in B0.** SciLean, Lanyon and lean-computational-mathematics are not imported into the B0 mathematical core.

## B0 scope

B0 contains only:

1. an exact-real scalar conservation-law contract;
2. an exact-real two-point numerical-flux evaluator plus separate consistency certificate;
3. a periodic finite-volume cell-average semidiscretization;
4. Forward Euler as the first one-step time method;
5. the Burgers physical flux;
6. the local Lax--Friedrichs/Rusanov two-point flux for Burgers;
7. generic proofs of consistency consequences, constant-state preservation and periodic conservation;
8. one assembled Burgers + Rusanov + Forward-Euler scheme theorem obtained by composition.

No array implementation is part of B0. Mathematical states are functions on the periodic finite index type.

## B0-P: scalar conservation law

A scalar conservation law exposes a physical flux

[
f : mathbb R 	o mathbb R.
]

The concrete Burgers law is

[
f(u)=rac{u^2}{2}.
]

## B0-F: two-point numerical flux

A two-point numerical flux has an evaluator

[
widehat f : mathbb R 	o mathbb R 	o mathbb R.
]

Consistency is a separate certificate:

[
operatorname{Consistent}(f,widehat f)
quadLongleftrightarrowquad
orall u, widehat f(u,u)=f(u).
]

B0 deliberately requires only the properties consumed by B0 proofs.

For Burgers, the selected first concrete flux is local Lax--Friedrichs/Rusanov:

[
a(u_L,u_R)=max(|u_L|,|u_R|),
]

[
widehat f_R(u_L,u_R)
=
rac{f(u_L)+f(u_R)}{2}
-rac{a(u_L,u_R)}{2}(u_R-u_L).
]

B0 proves exact consistency with the Burgers physical flux.

## B0-G: periodic uniform finite-volume state

Let the cell index type be `ZMod N` with nonzero `N`. The mathematical state is

[
u : operatorname{ZMod}(N) 	o mathbb R.
]

Let (Delta x 
e 0) for the algebraic operator and (Delta x>0) for its physical interpretation. The semidiscrete flux-difference operator is

[
L_i(u)
=
-rac{
widehat f(u_i,u_{i+1})
-
widehat f(u_{i-1},u_i)
}{Delta x}.
]

The implementation must keep the periodic shift explicit enough that the total-sum theorem is a finite reindexing/telescoping proof, not an assumed conservation axiom.

## B0-C: periodic conservation

For every state and every two-point flux,

[
sum_i L_i(u)=0
]

provided (Delta x
e0).

This theorem is flux-generic and does not require consistency.

Consequently, for common time step (Delta t), Forward Euler preserves the total cell-average sum:

[
sum_i u_i^{n+1}=sum_i u_i^n.
]

For constant (Delta x), derive preservation of the discrete integral

[
Delta xsum_i u_i.
]

## B0-K: constant-state preservation

For every consistent two-point numerical flux and every constant (c),

[
L_i(uequiv c)=0.
]

Forward Euler therefore preserves constant states exactly.

The final assembled Burgers/Rusanov theorem must be obtained by composition of the generic consistency and finite-volume/time-integration results, not by a Burgers-specific direct proof.

## B0-T: Forward Euler

Define

[
u_i^+
=
u_i+Delta t,L_i(u).
]

B0 proves only:

- total-sum preservation when the semidiscrete total sum is zero;
- constant-state preservation when the RHS vanishes.

No temporal-order, CFL, monotonicity, TVD, positivity, entropy or convergence claim is made in B0.

## Frozen module layout

```text
CFDLean/
  Burgers/
    Core/
      ConservationLaw.lean
      NumericalFlux.lean
      PeriodicGrid.lean
    Flux/
      Rusanov.lean
    FiniteVolume/
      FirstOrder.lean
      Conservation.lean
    Time/
      ForwardEuler.lean
    Schemes/
      RusanovForwardEuler.lean
    Controls.lean
```

The modules under `Core`, `FiniteVolume` and `Time` remain scalar-law generic wherever possible. `Flux/Rusanov.lean` and `Schemes/RusanovForwardEuler.lean` instantiate Burgers.

## Dependency policy

B0 imports Mathlib and existing CFD_Lean utility code only when the imported abstraction is genuinely generic.

No direct dependency on SciLean, Lanyon's Burgers development or lean-computational-mathematics is introduced in B0.

Later interop modules may prove correspondence with upstream definitions. Before independently reproving a substantial upstream theorem, a later stage must check whether an import, adapter theorem or upstream generalization is preferable.

## Proof-carrying component rule

A numerical component added after B0 should expose:

1. its mathematical evaluator/definition;
2. exact assumptions for each claimed property;
3. proofs of the properties required by the interfaces it implements;
4. source/reference correspondence when the component comes from literature.

Generic scheme theorems consume property certificates rather than inspect implementation details.

## Explicitly excluded from B0

B0 does **not** claim or implement:

- entropy-solution convergence;
- a discrete entropy inequality;
- monotonicity or TVD;
- any CFL restriction or CFL estimator;
- Godunov, HLL or higher-order fluxes;
- MUSCL, slope limiters or WENO;
- SSP Runge--Kutta;
- viscous Burgers;
- two-dimensional Burgers;
- floating-point semantics or rounding-error bounds;
- array, mutable-memory, SIMD, GPU or generated-C refinement;
- equivalence to an external Burgers formalization;
- automatic extraction/formalization of a paper.

## Frozen B0 result IDs

| ID | Required result |
| --- | --- |
| B0-P | Burgers physical-flux definition and selected equation convention |
| B0-F | Rusanov definition and consistency |
| B0-C | Generic periodic flux-difference total-sum cancellation |
| B0-K | Generic constant-state semidiscrete preservation from flux consistency |
| B0-T | Generic Forward-Euler conservation and constant-state composition |
| B0-S | Assembled Burgers/Rusanov/Forward-Euler constant-state and total-sum certificates |

Independent implementation review remains separate from implementation authorization.
