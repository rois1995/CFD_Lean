# Burgers B0: module layout after MR-1 (amendment of 2026-11-25)

The frozen contract `specifications/Burgers-B0.md` is not changed. This note replaces only its section "Frozen module
layout". The user asked for this change on 2026-11-25: adapt the B0 work to the layered folders of `main`
(MR-1, `specifications/MR.md`) and to Lean v4.36.0, without a new mathematical claim.

## Rule

The same rule as MR-1: each module moves to the folder of its main catalog layer. Namespaces, declaration names and
theorem types do not change. Frozen decision 2 of the contract ("Burgers is isolated under `CFDLean.Burgers`") now
applies to the namespace `CFDLean.Burgers`, not to a folder.

## Module map

| Old module (branch tip bb21358, Lean v4.19.0) | New module | Layer |
|---|---|---|
| `CFDLean.Burgers.Core.ConservationLaw` | `CFDLean.Physics.Scalar.ConservationLaw` | Physics models |
| `CFDLean.Burgers.Flux.Rusanov` (`physicalFlux`, `law`) | `CFDLean.Physics.Burgers.Flux` | Physics models |
| `CFDLean.Burgers.Core.PeriodicGrid` | `CFDLean.Discrete.Periodic.Grid` | Discrete operators |
| `CFDLean.Burgers.FiniteVolume.FirstOrder` | `CFDLean.Discrete.Periodic.FiniteVolume` | Discrete operators |
| `CFDLean.Burgers.FiniteVolume.Conservation` | `CFDLean.Discrete.Periodic.Conservation` | Discrete operators |
| `CFDLean.Burgers.Core.NumericalFlux` | `CFDLean.Schemes.Scalar.NumericalFlux` | Schemes |
| `CFDLean.Burgers.Flux.Rusanov` (namespace `Rusanov`) | `CFDLean.Schemes.Burgers.Rusanov` | Schemes |
| `CFDLean.Burgers.Schemes.RusanovForwardEuler` | `CFDLean.Schemes.Burgers.RusanovForwardEuler` | Schemes |
| `CFDLean.Burgers.Controls` | `CFDLean.Schemes.Burgers.Controls` | Schemes |
| `CFDLean.Burgers.Time.ForwardEuler` | `CFDLean.Time.ForwardEuler` | Time |
| `CFDLean.Burgers` (umbrella) | removed; `CFDLean.lean` imports every module | |
| `CFDLean.Verification.BurgersB0Challenge`, `.BurgersB0Verify` | unchanged | trusted statements and bridge |

## Changes that are not `import` lines

1. `Flux/Rusanov.lean` is split in two files: the physical flux (`physicalFlux`, `law`) and the numerical flux
   (namespace `Rusanov`). The declarations are the same text.
2. `Mathlib.Data.Real.Basic` is a deprecated module name in the pinned Mathlib. The four files that imported it now
   import `Mathlib.Basic.Real.Basic`. This includes the trusted statement file; its definitions are the same text.
3. One control example in `Controls.lean` did not compile with Lean v4.36.0 (`simpa`). It is now the direct term
   `Rusanov.consistent 3`. The statement of the example is the same.

Review command: `git diff -M bb21358 HEAD -- CFDLean`.

## Reuse of the MR-1 core

No Burgers definition is replaced by a core definition in B0:

- `CFDLean.Num.antisymmetric_pairFlux` (`CFDLean/Entropy/PairFlux.lean`) gives conservation and entropy production of
  antisymmetric pair fluxes on a finite node set. The periodic flux difference is an instance of it. The B0 proof
  uses one Mathlib reindexing lemma (`Fintype.sum_equiv`) and is shorter than an adapter. The adapter is useful for
  the entropy layer (B4), where the production identity is necessary.
- `CFDLean.Time.euler` (M5) is the lumped step for the Euler equations on `Conservative 3` with dual volumes. It is not
  generic. The scalar Forward Euler step stays a separate definition; M5 sources are not changed.
- `CFDLean.Assembly.Interfaces` and `CFDLean.Num.WMesh` are edge and simplex mesh structures in `d` dimensions with
  boundaries. A periodic 1D cell grid is not an instance without new geometry.

## New verification layer

- `specifications/Burgers-B0-results.json` binds each frozen result ID to its declarations. `scripts/verify.py` checks
  the bindings, the contract hash, the hash of the trusted statement file, its Mathlib-only imports and the bridge
  theorem types. The catalog (`catalog/theorems.json`) lists the 12 promised B0 theorems with status `pending`.
- `Challenges/BurgersB0.lean` and `Challenges/BurgersB0.comparator.json` are the input of
  `lake comparator --paranoid --config Challenges/BurgersB0.comparator.json`. The comparator checks that each bridge
  theorem has the statement of the challenge, uses only the three standard axioms, and is accepted by Lean's kernel
  and by five external checkers, in a `bwrap` sandbox.
