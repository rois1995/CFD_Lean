# Working in CFD_Lean

Use a branch and a pull request for every repository change. Start with [current status](roadmap/CURRENT.md) and
[next work](roadmap/NEXT.md), then use the [architecture](ARCHITECTURE.md) and [concept map](docs/CONCEPTS.md)
to locate the modules in scope.

- For a milestone, read its contract, approval and result map in [specifications](specifications/), its proof map in
  [references](references/) and the latest applicable record in [reviews](reviews/). Frozen contracts, trusted
  statements and independent verdicts govern scope and acceptance. Roadmap prose summarizes them.
- Preserve accepted statements, source and revision pins, and the archived evidence. For a change to frozen scope, use
  the milestone amendment workflow in [CONTRIBUTING.md](CONTRIBUTING.md). Standing implementation authorization and
  independent acceptance are distinct decisions.
- Maintain [catalog/theorems.json](catalog/theorems.json) alongside result bindings when they change. Regenerate
  `catalog/README.md` with `python3 scripts/catalog.py` and machine evidence with `python3 scripts/verify.py`.
  Treat `evidence/raw-types.json` as a pin. See the [artifact rules](CONTRIBUTING.md#artifacts-and-source-of-truth)
  for the difference between regenerated evidence and preserved review bundles.
- For documentation, check links, whitespace and the diff scope. Keep the evidence manifest current when a covered
  document changes. For Lean or verification changes, run the [applicable checks](CONTRIBUTING.md#validation), including
  the sandboxed comparator for affected challenges.
- In the PR, give the milestone or work package, what changed, checks run and any pending review. Use the actual
  candidate commit when preparing a reviewer handoff.
