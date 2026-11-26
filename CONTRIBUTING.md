# Contributing to CFD_Lean

Give the milestone or roadmap item, scope, and validation results in the PR description. The
[architecture guide](ARCHITECTURE.md) shows where code belongs. Match adjacent module, namespace and declaration
naming, and use [the root umbrella](CFDLean.lean) for new public library exports when applicable.

## Branches and releases

- Base task branches on `develop` and target `develop` with the PR. [Integration CI](.github/workflows/integration.yml)
  builds the package and executable, runs the verifier and fixtures, and compares committed evidence.
- Promote `develop` to `main` through a release PR. [Release verification](.github/workflows/release.yml) runs the
  integration checks and every trusted challenge with the paranoid comparator. Use a merge commit for the release.
- For an emergency fix, branch `hotfix/<topic>` from `main` and open a PR into `main` through the same release gate.
  Bring `main` back into `develop` through an integration PR after a release or hotfix to keep the branches aligned.
- Use PRs for all changes to `develop` and `main`. Update the PR branch against the target and resolve review
  conversations before merging.

Tag a verified release with an annotated `vMAJOR.MINOR.PATCH` tag on its exact `main` merge commit. Record that commit,
the passing release PR and the catalog, specification and evidence paths in the release notes. Build `burgers1d` from
the tagged revision for the release executable. Scientific acceptance remains recorded in the milestone review records.

## Milestone workflow

1. Read the current contract, result map, traceability and review record. For a new milestone or a change in scientific
   scope, record the proposed claims, hypotheses and exclusions, then freeze the approved scope and review checkpoint.
   Follow the [standing authorization](reviews/Standing_Authorization.md) and the approval record for the milestone.
2. Implement the agreed definitions and proofs. Bind the promised results to qualified theorem names and modules.
   Have an AI statement reviewer check each new or changed promised statement before merge. Where the milestone uses
   trusted challenges, check the trusted statement, bridge and comparator config together.
3. Run the checks below and record their results. For independent review, provide the exact candidate commit, frozen
   claims, proof map and replay instructions. Preserve the reviewer verdict with that revision.

The catalog uses `accepted` for independently accepted results, `pending` for implementation candidates awaiting
independent review, and `candidate` for contributions such as MC-N and JST1. A green build, a merge and an AI statement
review are implementation evidence. Record independent acceptance when the reviewer verdict is available.

## Artifacts and source of truth

| Location | How to maintain it |
|---|---|
| [Specifications](specifications/), trusted inputs and accepted pins | Frozen scope and trust records. Use a scoped amendment for an approved change and preserve earlier records. |
| [References](references/) and [roadmap](roadmap/) | Maintained navigation, proof traceability and plans. Use contracts and verdicts for exact scope and acceptance. |
| [Reviews](reviews/) and published replay bundles | Preserve the original payloads and hashes. Append later decisions and follow-ups as separate records. |
| [catalog/theorems.json](catalog/theorems.json) | Maintained theorem metadata that the verifier checks against promised results. Generate [catalog/README.md](catalog/README.md) with `python3 scripts/catalog.py`. |
| [Evidence](evidence/) | Regenerate active audit outputs and `SHA256SUMS` with `python3 scripts/verify.py`. `raw-types.json` is a pinned input to ordinary verification. A reviewed type change uses the verifier's `--record-raw-types` procedure and updates its pin. |

## Validation

For documentation changes, check relative links and run `git diff --check`. Review the file list for scope. If a document
is covered by [evidence/SHA256SUMS](evidence/SHA256SUMS), regenerate the manifest with the verifier and check the diff.

For Lean, contracts or verification tooling, use the pinned [Lean toolchain](lean-toolchain) and [Lake manifest](lake-manifest.json).
Run the following from the repository root. See the [shared verification workflow](.github/workflows/lean-verification.yml)
for the CI checks.

```bash
lake build
python3 -m unittest discover -s scripts -p test_verify.py
python3 scripts/catalog.py --check
python3 scripts/verify.py
sha256sum -c evidence/SHA256SUMS
```

The verifier builds the package and bridges, runs [KernelAudit.lean](KernelAudit.lean), and checks frozen contracts, the
catalog and pinned types. Inspect regenerated evidence against the PR's intended changes. When reviewing an already
published candidate, check its committed hashes before regeneration as well.

For a changed challenge or bridge, run the applicable `lake comparator --paranoid` config with the `bwrap` sandbox.
Use this command for B0.

```bash
lake comparator --paranoid --config Challenges/BurgersB0.comparator.json
```

For a driver or kernel change, also build `burgers1d` and exercise the affected options. For a frozen Euler checkpoint,
follow its [replay instructions](references/Euler-Milestones.md). Whole-build `lake check --paranoid` is reserved for an
explicit request, as the external checkers can require substantial RAM and time.
