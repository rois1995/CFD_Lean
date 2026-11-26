# Roadmap: next steps

This file contains work that is actionable or close enough to guide near-term implementation. Long-horizon ideas
belong in `FUTURE.md`; persistent architectural rules belong in `PRINCIPLES.md`.

Status date: 2026-11-26.

## Completed work package 0 - branch governance and release workflow

The protected integration and release flow is in use. [Integration PR #14](https://github.com/rois1995/CFD_Lean/pull/14) ·
[Release PR #15](https://github.com/rois1995/CFD_Lean/pull/15) · [Sync PR #16](https://github.com/rois1995/CFD_Lean/pull/16)

### Branch flow

```text
feature / milestone branch
        |
        | pull request + ordinary CI
        v
      develop
        |
        | release pull request + full paranoid verification
        v
       main
        |
        v
   version / release tag
```

Branch semantics:

- **feature branches:** experimental or in-progress work;
- **`develop`:** integrated code that builds and passes the ordinary verification stack;
- **`main`:** release/reference-quality state that has passed the full release gate;
- scientific acceptance remains separate from Git branch status: merging to `main` does not by itself make theorem
  statements independently accepted.

### Deliverables

- [x] Create `develop` from `main`.
- [x] Protect both `develop` and `main` against direct pushes, force pushes, and deletion, and require pull requests.
- [x] Require the ordinary CI gate for PRs into `develop`.
- [x] Require the full release and paranoid gate for PRs into `main`.
- [x] Split the original GitHub Actions workflow into ordinary integration CI and release verification. Release
  verification runs `lake comparator --paranoid` for every trusted challenge.
- [x] Run required release checks on every PR into `main`.
- [x] Require an up-to-date PR branch and resolved review conversations before merge.
- [x] Document the hotfix path and the PR that brings `main` back into `develop`.
- [x] Define the release tag convention so a tag identifies an exact `main` commit with its theorem catalog,
  specifications, executable and verification evidence.
- [x] Update `AGENTS.md` and contributor guidance to require PRs for changes to `main` and `develop`.
- [x] Keep CI acceptance and scientific acceptance distinct in documentation and automation.
- [x] Add lightweight Integration CI for navigation-only Markdown changes.
- [x] Add a repository-owner PR-only override for required CI on `develop` and `main`.

### Protection policy

- `develop`: PR required, ordinary CI required, up-to-date branch required, conversations resolved, force pushes
  and deletion disabled.
- `main`: PR required, full release/paranoid verification required, up-to-date branch required, conversations
  resolved, force pushes and deletion disabled; normally only release PRs from `develop` (plus emergency hotfixes)
  should target it.

The owner can explicitly override the CI rules on either branch when merging a PR. [CI override procedure](../CONTRIBUTING.md#owner-override-for-ci)

Do not require signed commits or linear history initially unless a concrete provenance/security requirement justifies
the extra friction. A release merge commit from `develop` to `main` is acceptable and provides a useful release
boundary.

Success criterion: routine development can proceed without direct writes to either long-lived branch, while
`develop` remains continuously integration-green and `main` remains a deliberately promoted, paranoid-checked
release/reference line.

## Repository navigation documentation

Start with the [README](../README.md), [architecture guide](../ARCHITECTURE.md),
[concept map](../docs/CONCEPTS.md), [contributor guide](../CONTRIBUTING.md) and [agent guide](../AGENTS.md).
Use pull requests for repository changes, including documentation.

## Priority 0 - close the review and trust backlog

Start the Burgers review at B0. Its kernel audit and result map cover the assembled `ZMod N` scheme B0-S. Decide during
review whether to add a dedicated trusted challenge for that scheme. [B0 trust boundary](../references/Burgers-B0.md#trusted-boundary-and-exclusions)

1. Complete independent implementation review of Burgers B0–B4, B3b, E0, E0b and E0c.
2. Human-review the trusted Burgers statements that currently have only agent review.
3. Complete the independent implementation review of M5.

## Deferred work package - generated navigation tooling

Revisit generated navigation after the first Burgers review checkpoint. Use the review to identify which lookups to
automate. Changes to Lean source layout, scripts or CI follow the normal validation workflow.

Deliverables:

1. Add umbrella Lean entry modules for major subsystems where useful (for example `CFDLean/Physics.lean`,
   `CFDLean/Geometry.lean`, `CFDLean/Discrete.lean`, `CFDLean/Schemes.lean`, `CFDLean/Time.lean`,
   `CFDLean/Exec.lean`, plus selected subsystem umbrellas such as Burgers or MedianDual).
2. Generate a module/import dependency index and graph from Lean imports rather than maintaining it by hand.
3. Add a lightweight architecture check that can detect forbidden dependency directions (for example mathematical
   layers importing `Exec`).
4. Generate milestone landing pages that connect contract, implementation modules, trusted statements, comparator,
   theorem count and acceptance status.
5. Add a small theorem/concept search CLI over the existing theorem catalog/result maps (filters such as theorem name,
   layer, milestone, module and status).
6. Prefer existing result maps/catalog metadata as the source of truth; do not manually duplicate milestone metadata
   across hundreds of declarations.
7. Run the ordinary validation stack after these changes: at minimum `lake build`, the repository verifier/fixtures
   affected by the change, and generated-file consistency checks; run broader CI when dependency-enforcement behavior
   changes.

The goal is to locate a concept, its authoritative artifacts, its status and its validation commands from the docs and
generated indexes.

## Priority 1 - shared 1D finite volume for Burgers and Euler

Start the next Euler proposal on the uniform periodic, cell-centered grid used by Burgers. Hold the geometry,
numerical flux family and time integrator fixed so that the state and physical model are the only changes.
This is a new line alongside the multidimensional median-dual M1–M6 milestones.

1. **Use the existing Euler physics in one dimension.** Specialize `Conservative d` and `physicalFlux` to
   `d = 1` and positive unit face orientation. The three conserved quantities are density, momentum and total
   energy. Use the existing ideal-gas pressure and admissibility domain. Start with homogeneous Burgers and Euler.
   A later balance law can supply a physical source and will need a discrete source contribution in its balance.
   [Euler state](../CFDLean/Physics/Euler/State.lean) · [Oriented flux](../CFDLean/Physics/Euler/PhysicalFlux.lean)
2. **Propose one first-order step with two instantiations.** Share the periodic neighbors, Rusanov flux formula,
   face-flux difference and Forward Euler update. The model supplies the physical flux and a speed estimate.
   Recover the existing Burgers choice exactly. For Euler, specify the endpoint estimate using velocity and sound
   speed on admissible states and state the speed hypothesis needed for each claim.
   [Burgers Rusanov](../CFDLean/Schemes/Burgers/Rusanov.lean) · [Periodic residual](../CFDLean/Discrete/Periodic/FiniteVolume.lean)
3. **First acceptance target.** Prove equality to the existing Burgers update for every state on the supported
   uniform periodic grids. For Euler, prove equal-state flux consistency, preservation of admissible constants and
   periodic conservation of mass, momentum and energy. Include a nonconstant control for face orientation and the
   update sign. Freeze the proposal before implementing these results.
4. **Advance both models through the same solver.** Reuse the existing SSP composition lemmas. Scope Euler
   density/pressure positivity under a specified CFL condition before claiming admissible multi-step evolution.
   Higher-order reconstruction and entropy require their own system hypotheses and proofs. For the executable
   milestone, run both models through one array traversal and time loop and prove exact-real refinement for each.
   Keep backend arithmetic separate from the conserved state and certify machine error under E1.
   [SSP](../CFDLean/Time/SSP.lean) · [Burgers refinement](../CFDLean/Exec/Refinement.lean)
5. **Extend dimension after the 1D comparison.** A periodic Euler density wave with constant pressure and velocity
   gives a first system benchmark with a known translated profile. Then exercise oriented face fluxes on a fixed 2D
   mesh. For the 3D median-dual method, use the existing Roe, geometry and boundary results. Any correspondence
   with a cell-centered method needs an explicit statement about the control volumes and transfers being compared.

### Non-uniform fixed 1D finite volume

Use Burgers to test geometry independently of the Euler model change. Apply the shared first-order step to both
models on this mesh once their uniform-grid specializations are established.

Target components:

1. Explicit 1D cell geometry: cell measure, centroid, left/right faces and face-to-centroid distances.
2. Scalar FV update with cell-dependent volumes rather than one global `dx`.
3. Volume-weighted conservation:
   `sum_i volume_i * u_i`.
4. Geometry-aware MUSCL reconstruction using distance-normalized differences and actual face offsets.
5. Proof that the current uniform formulas are recovered as a specialization.
6. Local CFL / bounds / TVD statements and a clear account of which B1--B3 lemmas remain reusable.
7. Avoid premature replacement of every current `Fin n` API: generalize only what the milestone actually exercises.

Success criterion: the extension should require local geometric generalization, not a rewrite of flux, entropy and time
composition layers.

## Priority 2 - E1 machine arithmetic strategy

The Burgers array kernels already use `Scalar α`, with `ScalarSign α` where a limiter needs a sign test. The current
refinement theorems cover the kernel interpreted over `ℝ`. The native driver selects Lean `Float` (binary64). E1 starts
with a design proposal defining an arithmetic backend and its refinement contract. Backend implementations follow
when the contract or a concrete use case justifies them. [Kernel](../CFDLean/Exec/Kernel.lean) ·
[Limiter kernel](../CFDLean/Exec/LimiterKernel.lean) · [Driver](../Main.lean)

| Capability | Scope for E1 |
|---|---|
| Kernel arithmetic (`Scalar`) | Minimal operations and constants used to advance the state, including `abs` and `max` for the Burgers flux. `ScalarSign` supplies the sign test for limiters that need it. |
| Runtime arithmetic (illustrative `RuntimeScalar`) | Parsing, formatting, conversions such as `Nat` to the backend scalar, and finite/NaN checks. Keep initialization, I/O and diagnostic reporting at the driver boundary. |
| Optional math | Operations such as `sqrt`, `sin`/`cos` and `exp`/`log`, required only by the component using them. The current driver uses `Float.sin` and `Float.acos` to initialize its sinusoid and `Float.abs` in its scaling and formatting. |
| Arithmetic certification | Relate backend values and operations to `ℝ`. State the domain, arithmetic and runtime assumptions, and the error bound or enclosure that a step or run would certify. |

The capability names illustrate design roles. Introduce an interface only when a concrete consumer needs one.

Lean v4.36.0 defines `Float` and `Float32` as wrappers around the bit-pattern models `Float.Model` (binary64) and
`Float32.Model` (binary32). Basic operations such as addition and division have logical definitions through those models
and native implementations at runtime. Driver functions such as `Float.sin` and `Float.acos` are opaque in the logic.
E1 should inventory the operations it relies on, use model definitions where applicable, and state the assumptions
linking the selected native operations to the model. A solver-level relation to `ℝ` is a separate proof obligation.
[Toolchain pin](../lean-toolchain) ·
[Pinned `Float` source](https://raw.githubusercontent.com/leanprover/lean4/v4.36.0/src/Init/Data/Float/Float.lean) ·
[Pinned `Float32` source](https://raw.githubusercontent.com/leanprover/lean4/v4.36.0/src/Init/Data/Float/Float32.lean)

Compare using the Lean models, a separate IEEE model or external verified arithmetic, and interval enclosures for a
reference run. The future backend family may include binary32, binary64, wider IEEE formats, arbitrary or
multiprecision arithmetic, interval arithmetic, and mixed precision with explicit conversions. Deterministic reference
arithmetic may use reproducible or exact accumulators for selected reductions.

## Priority 3 - verified-run provenance and basic solver output

These are low-risk executable features that prepare the solver for reference simulations without changing numerical
mathematics.

1. Add step- or time-based solution snapshots, not only final `--dump`.
2. Define a machine-readable run manifest containing at least commit, scheme, parameters, arithmetic mode and input
   hashes.
3. Keep diagnostics separate from solution-field output.
4. Plan checkpoint/restart metadata so a restarted run can retain provenance.

The driver itself can remain outside the strongest proof boundary initially; the format should nevertheless be
designed so later certification can attach to it.

## Priority 4 - remaining mathematical Burgers extensions

Candidates, to be proposed/frozen separately:

- fully discrete entropy inequality;
- sharper CFL bounds for B1 and B3;
- accuracy/order statements;
- eventual convergence statements;
- adapter between the periodic scalar operator and `CFDLean.Num.antisymmetric_pairFlux`;
- B5 paper correspondence once the reference sources are chosen.

## Priority 5 - M6 composition

Keep M6 on the median-dual track. When proposing it, reconcile the one-step composition in the
[original milestone table](../specifications/M2-proposal.md) with the assembled step already supplied by
[M5](../references/M5.md), and specify any multi-step claim and its admissibility hypotheses separately.

Keep the generic time-evolution interfaces compatible with future variable-step and implicit methods.

## Priority 6 - numerical-core and paper housekeeping

- Narrow `CFDLean.Num.Basic`'s broad `import Mathlib` where practical.
- Move remaining generic JST results (P1-5.4b, P1-5.8) into the numerical core when justified.
- Add the archive pointer note in JST_Paper_Lean.
- Continue paper-1 gaps that need new mathematics: non-affine (trilinear) mixed cells. Simplex integration is done
  (JST1 P6).
- Keep the theorem catalog and raw-type evidence synchronized with every milestone.
