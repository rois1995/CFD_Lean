# Contributing to CFD_Lean

Give the milestone or roadmap item, scope, and validation results in the PR description. The
[architecture guide](ARCHITECTURE.md) shows where code belongs. Match adjacent module, namespace and declaration
naming, and use [the root umbrella](CFDLean.lean) for new public library exports when applicable.

In the PR that completes a roadmap item, check it off with `- [x]` in [roadmap/NEXT.md](roadmap/NEXT.md).
For partial work, check off the completed deliverables and keep the overall item open.

## Branches and releases

- Base task branches on `develop` and target `develop` with the PR. [Integration CI](.github/workflows/integration.yml)
  builds the package and executable, runs the verifier and fixtures, and compares committed evidence.
  To also run the trusted challenges with the paranoid comparator on a `develop` PR, add the `paranoid` label to the
  PR. You can also start [the paranoid workflow](.github/workflows/paranoid.yml) for a branch from the Actions tab.
  On a PR it skips the paper-1 challenge (JST1) unless the PR changes paper-1 files, and it builds only the modules
  the selected challenges need. This check is optional, and the release PR runs it again with every challenge.
- Integration CI reuses the compiled modules of unchanged files from a build cache (restored from the same PR or
  from `develop`, which [Develop build cache](.github/workflows/develop-cache.yml) refreshes after each merge). Lake
  validates its saved build traces and rebuilds artifacts whose recorded inputs no longer match, so source and import
  changes invalidate affected modules transitively. Release verification never uses this cache and builds everything
  from scratch.
- Promote `develop` to `main` through a release PR. [Release verification](.github/workflows/release.yml) runs the
  integration checks and every trusted challenge with the paranoid comparator. Use a merge commit for the release.
- For an emergency fix, branch `hotfix/<topic>` from `main` and open a PR into `main` through the same release gate.
  Bring `main` back into `develop` through an integration PR after a release or hotfix to keep the branches aligned.
- Use PRs for all changes to `develop` and `main`. Update the PR branch against the target and resolve review
  conversations before merging.

### Owner override for CI

The repository owner `rois1995` can explicitly override required CI on PRs into `develop` or `main`.
Use `gh pr merge <number> --admin --merge --match-head-commit <reviewed-head-sha>` for the exact PR head reviewed.
This also bypasses GitHub's up-to-date check. On `main`, it bypasses the CI check of the release PR source, so verify
that the PR comes from `develop` or a same-repository `hotfix/` branch. Record the reason and any checks run in the PR.
Both branches still require pull requests and resolved review conversations, and block force pushes and deletion.

### Release tags

Tag a verified release with an annotated `vMAJOR.MINOR.PATCH` tag on its exact `main` merge commit. Record that commit,
the passing release PR and the catalog, specification and evidence paths in the release notes. Build `fv1d` from
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

For new or slow proofs, follow the [Lean performance guide](docs/LEAN_PERFORMANCE.md) (measured patterns for fast
kernel checks, memory cap, measuring build time).

For documentation changes, check relative links and run `git diff --check`. Review the file list for scope. If a document
is covered by [evidence/SHA256SUMS](evidence/SHA256SUMS), regenerate the manifest with the verifier and check the diff.

For `develop` PRs that only add or edit ordinary Markdown in `docs/`, `roadmap/`, `AGENTS.md`, `ARCHITECTURE.md`,
`CONTRIBUTING.md`, or `TODO.md`, Integration CI runs the link, anchor, whitespace, and checksum checks without building
Lean. Other changes use full integration verification. Release PRs use the full release gate.

### CI first

Use GitHub CI as the main check for Lean, contracts and verification tooling. Push the task branch and open a draft PR
into `develop` as soon as there is new code, then iterate on what CI reports. Quick local checks of the files you
changed are welcome for fast feedback (`lake env lean Path/File.lean`, under the memory cap of the
[performance guide](docs/LEAN_PERFORMANCE.md)); avoid routine full local builds and verifier runs.

The evidence files are generated by `scripts/verify.py` and must be committed, but CI cannot commit. When the verifier
or the evidence comparison fails in Integration CI, CI regenerates a complete evidence set and uploads it as the
artifact `regenerated-evidence` (kept 7 days). After a verifier failure it first records the raw types and, in its own
copy only, sets the new pin; the full verifier must then pass, otherwise nothing is uploaded.

```bash
gh run download <run-id> -n regenerated-evidence -D /tmp/evidence   # run id: gh run list --branch <branch>
cp /tmp/evidence/* evidence/ && rm -f evidence/RAW_TYPES_SHA256.txt   # then review the diff
```

Check the diff before committing: the evidence must change only where the PR changed theorems. If `raw-types.json`
changed, it must contain only additions (or reviewed changes) for the PR's theorems; then set `RAW_TYPES_SHA256` in
`scripts/verify.py` to the value in the artifact's `RAW_TYPES_SHA256.txt`. Push again; the next run must be green.

### Local checks

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

For a driver or kernel change, also build `fv1d` and exercise the affected options. For a frozen Euler checkpoint,
follow its [replay instructions](references/Euler-Milestones.md). Whole-build `lake check --paranoid` is reserved for an
explicit request, as the external checkers can require substantial RAM and time.
