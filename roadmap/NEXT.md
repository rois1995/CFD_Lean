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

1. [x] Complete independent implementation review of Burgers B0–B4, B3b, E0, E0b and E0c.
   [Review](../reviews/Burgers-Implementation/Review.md). B0-S gets no dedicated trusted challenge; see the review.
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

FV1D shares the uniform periodic, cell-centered method between Burgers and Euler. The multidimensional
median-dual M1–M6 milestones retain their own geometry and scope.

1. [x] **Specialize M1 physics to one dimension.** The three conserved quantities are density, x-momentum and
   total energy. The physical flux uses the positive unit face and the existing pressure and admissibility.
   [Euler adapter](../CFDLean/Schemes/Euler/FV1D.lean)
2. [x] **Share the first-order step.** Both models supply their physical flux and a two-state speed to the same
   periodic Rusanov and Forward Euler formulas. The sums of the three Euler quantities follow by projection of
   a single state conservation theorem. [Shared method](../CFDLean/Discrete/Periodic/Rusanov.lean)
3. [x] **Implement the four frozen claims and three-cell control.** [Independent review](../reviews/FV1D/Acceptance.md) accepted all four claims. [Contract](../specifications/FV1D.md) · [Proof map](../references/FV1D.md)
4. **Select one physical model per run.** The planned executable takes an explicit model argument, for example
   `lake exe fv1d --model burgers` or `lake exe fv1d --model euler`. Dispatch once in the driver and advance the
   selected state through the shared array traversal and time loop. Preserve `burgers1d` as a Burgers entry point
   with its existing arguments and defaults. Compare its output with the equivalent `fv1d --model burgers` run.
   Reuse the existing SSP composition lemmas. Scope Euler density/pressure positivity under a specified CFL
   condition before claiming admissible multi-step evolution. Higher-order reconstruction and entropy require
   their own system hypotheses and proofs. Prove exact-real refinement for each model and certify machine error
   under E1. Keep backend arithmetic separate from the conserved state.
   [SSP](../CFDLean/Time/SSP.lean) · [Burgers refinement](../CFDLean/Exec/Refinement.lean)
5. **Extend dimension after the 1D comparison.** A periodic Euler density wave with constant pressure and velocity
   gives a first system benchmark with a known translated profile. Then exercise oriented face fluxes on a fixed 2D
   mesh. For the 3D median-dual method, use the existing Roe, geometry and boundary results. Any correspondence
   with a cell-centered method needs an explicit statement about the control volumes and transfers being compared.
   [Periodic Euler density-wave reference case](../benchmarks/fv1d/README.md)

### Non-uniform fixed 1D finite volume

**Status.** FVN is implemented: first-order and MUSCL steps on a fixed non-uniform periodic mesh, eight frozen
results, three exact controls and a trusted challenge for the scalar claims. Independent implementation review is
pending. [Contract](../specifications/FV1D-nonuniform.md) · [Proof map](../references/FV1D-nonuniform.md)

Use Burgers to test geometry independently of the Euler model change. Apply the shared first-order step to both
models on this mesh once their uniform-grid specializations are established.

Target components (delivered by FVN; see [What FVN showed](../references/FV1D-nonuniform.md#what-fvn-showed)):

1. [x] Explicit 1D cell geometry: cell measure, centroid, left/right faces and face-to-centroid distances. Delivered
   as widths only: a 1D centroid is the cell midpoint, so the centroid distances follow from the widths.
2. [x] Scalar FV update with cell-dependent volumes rather than one global `dx`.
3. [x] Volume-weighted conservation:
   `sum_i volume_i * u_i`.
4. [x] Geometry-aware MUSCL reconstruction using distance-normalized differences and actual face offsets.
5. [x] Proof that the current uniform formulas are recovered as a specialization.
6. [x] Local CFL / bounds / TVD statements and a clear account of which B1--B3 lemmas remain reusable.
7. [x] Avoid premature replacement of every current `Fin n` API: generalize only what the milestone actually exercises.
   FVN adds new modules only.

Success criterion: the extension should require local geometric generalization, not a rewrite of flux, entropy and time
composition layers.

### Burgers line after FVN: kernels, general driver, retiring `burgers1d`

Burgers stays the line where shared capabilities are built first; Euler follows on merged shared code.

1. **FVNA** — executable array kernels on the non-uniform mesh and their exact-real refinement (first order shared
   by Burgers and Euler; Burgers MUSCL with every limiter and SSPRK2/SSPRK3), with the FVN guarantees transferred to
   the arrays. No driver change. [Proposal](../specifications/FV1D-nonuniform-array-proposal.md)
2. **General driver** — `lake exe fv1d --model burgers|euler` with every current `burgers1d` capability (first
   order, MUSCL with limiters, SSPRK3, diagnostics, dump) plus a non-uniform mesh option. Include a check that
   `fv1d --model burgers` reproduces the `burgers1d` output on the same input.
3. **Retire `burgers1d`** — once step 2 is accepted, amend the E0 and E0b driver claims (and the FVA "preserve
   `burgers1d`" sentence) so that `fv1d --model burgers` is the Burgers entry point; remove `burgers1d` or keep it as
   a thin alias. Update the CI smoke test accordingly.

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
- Paper 1: all planned statements proved (JST1 P1-P8, 121 of 121): non-affine mixed cells (P7), the Kuhn-split
  counterexample and the interior-vertex failure in a multi-cell mesh (P8), simplex integration (P6). Paper gaps
  G1-G8 are fixed in the paper (2026-11-27); two cosmetic P6 notes and one count ("56" for 96 sub-tetrahedra)
  remain for the paper session.
- Keep the theorem catalog and raw-type evidence synchronized with every milestone.
