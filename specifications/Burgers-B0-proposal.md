# Burgers B0 proposal: composable exact-real finite-volume core

Status: **proposal for review; no Burgers implementation is frozen by this document**.

## Purpose

Add a new `CFDLean.Burgers` development that serves as the first reusable, composable numerical-scheme layer for scalar conservation laws. This work is intentionally isolated from the accepted compressible-Euler M1--M4 chain and the current M5 implementation review.

The first target is the one-dimensional inviscid Burgers equation

[
u_t + left(rac{u^2}{2}ight)_x = 0
]

on a periodic uniform mesh, using exact real arithmetic.

The architectural objective is broader than one Burgers solver: new numerical methods should be assembled from components whose mathematical contracts are already proved, so that later PRs inherit generic results instead of reproving them solver by solver.

## B0 scope

B0 contains only:

1. an exact-real scalar conservation-law contract;
2. an exact-real two-point numerical-flux contract;
3. a periodic finite-volume cell-average semidiscretization;
4. Forward Euler as the first one-step time method;
5. the Burgers physical flux;
6. the local Lax--Friedrichs/Rusanov two-point flux for Burgers;
7. generic proofs of consistency consequences, constant-state preservation and periodic conservation;
8. one assembled Burgers + Rusanov + Forward-Euler scheme theorem obtained by composition.

No array implementation is part of B0. Mathematical states are functions on a finite periodic index type.

## Exact mathematical contracts

### B0-P: scalar conservation law

Proposed namespace: `CFDLean.Burgers.Core`.

A scalar conservation law should expose a physical flux

[
f : mathbb R 	o mathbb R.
]

The concrete Burgers law is

[
f(u)=rac{u^2}{2}.
]

The core abstraction should remain generic enough that the finite-volume and time-integration proofs do not mention Burgers.

### B0-F: two-point numerical flux

A two-point flux has an evaluator

[
widehat f : mathbb R 	o mathbb R 	o mathbb R
]

and a consistency theorem

[
widehat f(u,u)=f(u).
]

B0 deliberately requires only the properties consumed by B0 proofs. Monotonicity, Lipschitz bounds, entropy stability and higher-order reconstruction interfaces belong to later stages.

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

B0 proves its exact consistency with the Burgers physical flux.

### B0-G: periodic uniform finite-volume state

Let the cell index type be a finite cyclic type with at least one cell. The mathematical state is

[
u : I 	o mathbb R.
]

Let (Delta x > 0). The semidiscrete flux-difference operator is

[
L_i(u)
=
-rac{
widehat f(u_i,u_{i+1})
-
widehat f(u_{i-1},u_i)
}{Delta x}.
]

The index representation should make periodic predecessor/successor identities explicit and should support finite-sum reindexing without introducing array bounds obligations.

The preferred first candidate is `ZMod N` with a nonzero-size condition, unless review finds a simpler finite cyclic representation that gives materially cleaner proofs.

### B0-C: periodic conservation

For every state and every two-point flux, prove the algebraic telescoping identity

[
sum_i L_i(u)=0.
]

This theorem is flux-generic: it does not require consistency.

Consequently, for common time step (Delta t), Forward Euler preserves the total cell-average sum:

[
sum_i u_i^{n+1}=sum_i u_i^n.
]

With constant cell width this is equivalent to preservation of the discrete integral
(Delta xsum_i u_i).

### B0-K: constant-state preservation

For every consistent two-point numerical flux and every constant (c),

[
L_i(uequiv c)=0.
]

Forward Euler therefore preserves constant states exactly.

The final assembled Burgers/Rusanov theorem must be obtained by composition of the generic consistency and finite-volume/time-integration results rather than by a Burgers-specific direct proof.

### B0-T: Forward Euler

Define the exact-real one-step update

[
u_i^+
=
u_i+Delta t,L_i(u).
]

B0 proves only:

- total-sum preservation when the semidiscrete sum is zero;
- constant-state preservation when the RHS vanishes.

No temporal-order, CFL, monotonicity, TVD, positivity, entropy or convergence claim is made in B0.

## Proposed module layout

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

The modules under `Core`, `FiniteVolume` and `Time` should remain scalar-law generic wherever possible. `Flux/Rusanov.lean` and `Schemes/RusanovForwardEuler.lean` are Burgers-specific instantiations.

No existing accepted Euler source file should be modified merely to support this development.

## Dependency policy

B0 imports Mathlib and existing CFD_Lean utility code only when the imported abstraction is genuinely generic.

No direct dependency on SciLean, Lanyon's Burgers development or lean-computational-mathematics is introduced in the mathematical core during B0.

Instead, later interop modules may prove correspondence with upstream definitions. This keeps the CFD_Lean semantic interface under project control while permitting theorem reuse after exact statement alignment is reviewed.

Before independently reproving a substantial upstream theorem, a later stage must check whether an import, adapter theorem or upstream generalization is preferable.

## Proof-carrying component rule

A numerical component added after B0 should expose:

1. its executable mathematical definition;
2. the exact assumptions under which each claimed property holds;
3. proofs of the properties required by the interfaces it implements;
4. source/reference correspondence when the component comes from literature.

Generic scheme theorems should consume these interfaces rather than inspect implementation details.

The intended future pattern is therefore:

```text
paper/source
    |
    v
formal component contract
    |
    v
proved component
    |
    v
generic composition theorem
    |
    v
assembled scheme certificate
```

The proof-generating agent is not trusted. Lean's kernel remains the proof checker.

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

These are later stages and must state their own contracts before implementation.

## Proposed B0 result IDs

| ID | Required result |
| --- | --- |
| B0-P | Burgers physical-flux definition and exact selected equation convention |
| B0-F | Rusanov definition and consistency |
| B0-C | Generic periodic flux-difference total-sum cancellation |
| B0-K | Generic constant-state semidiscrete preservation from flux consistency |
| B0-T | Generic Forward-Euler conservation and constant-state composition |
| B0-S | Assembled Burgers/Rusanov/Forward-Euler constant-state and total-sum certificates |

## Review questions

1. Is `ZMod N` the right first periodic cell index, or should B0 use a custom finite cyclic grid abstraction?
2. Should the core numerical-flux structure carry consistency as a field, or should properties be separate predicates/typeclasses so that the same evaluator may carry several independently proved certificates?
3. Should `ScalarConservationLaw` be introduced already in B0, or is a physical-flux parameter sufficient until a second scalar PDE exists?
4. Should total conservation be stated for the raw sum first and derive (Delta x)-weighted conservation, or should the public theorem directly use the discrete integral?
5. Are there any existing Mathlib or accepted CFD_Lean abstractions that should be reused rather than duplicated?

Implementation should begin only after these interface choices are reviewed or explicitly accepted.
