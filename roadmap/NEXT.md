# Roadmap: next steps

This file contains work that is actionable or close enough to guide near-term implementation. Long-horizon ideas
belong in `FUTURE.md`; persistent architectural rules belong in `PRINCIPLES.md`.

Status date: 2026-11-26.

## Immediate work package 0 - branch governance and release workflow

Introduce a protected integration/release branch model before further routine development.

Target flow:

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

Deliverables:

1. Create `develop` from the current `main`.
2. Protect both `develop` and `main` against direct/force pushes and deletion; require pull requests.
3. Require the ordinary CI gate for PRs into `develop`.
4. Require the full release/paranoid gate for PRs into `main`.
5. Split the current monolithic GitHub Actions workflow into at least:
   - ordinary CI for feature/milestone PRs targeting `develop`;
   - release verification for `develop -> main`, including every trusted challenge and
     `lake comparator --paranoid`.
6. Keep required release checks free of restrictive path filters that could cause a required check to be skipped.
7. Require the target branch to be up to date before merge and require review conversations to be resolved.
8. Document the hotfix path:
   `main -> hotfix/... -> PR to main -> full release gate -> merge/back-port main into develop`.
9. Define the release/tagging convention so a tag identifies an exact `main` commit together with its theorem
   catalog, specifications, executable and verification evidence.
10. Update `AGENTS.md` / contributor guidance so agents and humans never write directly to `main` or `develop`
    after this migration.
11. Keep CI acceptance and scientific acceptance explicitly distinct in documentation and automation.

Suggested protection policy:

- `develop`: PR required, ordinary CI required, up-to-date branch required, conversations resolved, force pushes
  and deletion disabled.
- `main`: PR required, full release/paranoid verification required, up-to-date branch required, conversations
  resolved, force pushes and deletion disabled; normally only release PRs from `develop` (plus emergency hotfixes)
  should target it.

Do not require signed commits or linear history initially unless a concrete provenance/security requirement justifies
the extra friction. A release merge commit from `develop` to `main` is acceptable and provides a useful release
boundary.

Success criterion: routine development can proceed without direct writes to either long-lived branch, while
`develop` remains continuously integration-green and `main` remains a deliberately promoted, paranoid-checked
release/reference line.

## Immediate work package A - documentation/navigation layer

Land the low-risk repository navigation improvements through the new feature-branch -> `develop` flow. This package changes documentation only and
must not alter Lean declarations, theorem statements, executable code or verifier behavior.

Deliverables:

1. Add `ARCHITECTURE.md` with the layer/dependency model, dependency rules and a "where should this code go?"
   decision tree.
2. Add `AGENTS.md` with repository-specific instructions for autonomous coding/review agents: what to read first,
   where contracts live, what is authoritative/frozen, generated-file rules, validation commands and what counts as
   done.
3. Add `CONTRIBUTING.md` for human contributors, including milestone/specification workflow, naming/location rules,
   review/acceptance states and validation expectations.
4. Add `docs/CONCEPTS.md`: a concept-to-code map (fluxes, reconstruction, conservation, entropy, time integration,
   geometry, execution/refinement, etc.).
5. Add concise README files at major subsystem boundaries where they materially improve orientation (for example
   `CFDLean/Exec/`, `CFDLean/Discrete/`, `CFDLean/Schemes/`, and `CFDLean/Geometry/MedianDual/`).
6. Shorten/restructure the root `README.md` so the first screen answers: what CFD_Lean is, what is verified today,
   what can be executed today, and where to navigate next. Move historical/reproduction detail to appropriate
   reference documents instead of deleting it.
7. Clearly mark generated versus authoritative/frozen documents wherever ambiguity could cause an agent or human to
   edit the wrong artifact.

Because this package is documentation-only, it needs only the ordinary integration gate once branch governance is in place; it does not require the full paranoid release gate by itself. Check broken links and accidental edits outside the intended files.

## Immediate work package B - generated/code-backed navigation tooling

After package A, add navigation helpers that touch Lean source layout, scripts or CI. These are still architecture/tooling
work rather than new CFD mathematics, but they receive the normal build/verifier/CI checks before landing.

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

Success criterion for A+B: a new human or agent should be able to answer "where is this concept?", "what is safe to
edit?", "what is the current status?", and "what validates this milestone?" without reconstructing the repository
structure from recursive search.

## Priority 0 - close the review / trust backlog

1. Complete the independent implementation review of M5.
2. Complete independent review of Burgers B0--B4, E0 and E0b.
3. Human-review the trusted Burgers statements that currently have only agent review.
4. Resolve the open B0 trusted-boundary question: the current trusted B0 statements do not separately state the
   assembled `ZMod N` scheme B0-S.

The mathematics is moving faster than independent acceptance. Closing this gap is important before many additional
solver layers accumulate.

## Priority 1 - non-uniform fixed 1D finite volume

Use a non-uniform fixed Burgers mesh as the next architectural stress test before ALE or AMR.

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

The executable already uses the same kernel shape at `Real` and `Float`, but only the real-arithmetic refinement is
proved.

Before committing to a large floating-point development, write a small design proposal comparing viable routes:

- a formal IEEE model and a theorem relating it to the executable operations;
- interval/enclosure arithmetic for a reference mode;
- reproducible/exact accumulator techniques for selected reductions;
- external verified arithmetic kernels with a narrow trusted/refinement interface.

The required deliverable is a precise statement of what a future `Float` result could be certified to mean.

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
- limiters beyond the current minmod region (e.g. MC, superbee);
- accuracy/order statements;
- eventual convergence statements;
- adapter between the periodic scalar operator and `CFDLean.Num.antisymmetric_pairFlux`;
- B5 paper correspondence once the reference sources are chosen.

## Priority 5 - M6 composition

Continue the original Euler roadmap with multi-step evolution on top of M5
(`specifications/M2-proposal.md`).

Keep the generic time-evolution interfaces compatible with future variable-step and implicit methods.

## Priority 6 - numerical-core and paper housekeeping

- Narrow `CFDLean.Num.Basic`'s broad `import Mathlib` where practical.
- Move remaining generic JST results (P1-5.4b, P1-5.8) into the numerical core when justified.
- Add the archive pointer note in JST_Paper_Lean.
- Continue paper-1 gaps that need new mathematics: non-affine (trilinear) mixed cells. Simplex integration is done
  (JST1 P6).
- Keep the theorem catalog and raw-type evidence synchronized with every milestone.
- Shorten the root README by moving historical detail into `references/` where useful.
