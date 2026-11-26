# Working in CFD_Lean

Open a pull request from a task branch into `develop` for routine work. Promote `develop` to `main` through a
release PR. Follow the [branch, hotfix and release instructions](CONTRIBUTING.md#branches-and-releases).
Start with [current status](roadmap/CURRENT.md) and [next work](roadmap/NEXT.md), then use the
[architecture](ARCHITECTURE.md) and [concept map](docs/CONCEPTS.md) to locate the modules in scope.

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
- Work CI first: push the task branch and open a draft PR into `develop` as soon as there is new code, and iterate on
  what CI reports. Locally, run at most quick single-file checks under a memory cap; take regenerated evidence from
  the CI artifact `regenerated-evidence` ([CI first](CONTRIBUTING.md#ci-first)).
- Before writing a proof that computes (`decide +kernel`, large case splits), read the
  [Lean performance guide](docs/LEAN_PERFORMANCE.md): brute force first, no `Kind` case split inside kernel loops,
  no raised `maxRecDepth`, a memory cap for every Lean run, and how to measure.
- For documentation, check links, whitespace and the diff scope. Keep the evidence manifest current when a covered
  document changes. For Lean or verification changes, run the [applicable checks](CONTRIBUTING.md#validation), including
  the sandboxed comparator for affected challenges.
- In the PR, give the milestone or work package, what changed, checks run and any pending review. Use the actual
  candidate commit when preparing a reviewer handoff.

## Arithmetic and execution

- Preserve arithmetic-polymorphic kernels such as `Scalar α`. Keep generic mathematics and numerical APIs independent
  of machine types such as `Float` and `Float32`. Select precision in the execution or refinement layer.
- Before extending `Scalar`, identify the kernel operation that requires the capability. Keep parsing, printing,
  conversions, finite and NaN checks, and math used only for initialization or diagnostics in the driver or backend.
  A sinusoidal initial condition can call `sin` in the driver while the solver kernel accepts the resulting values.
- Treat binary32, binary64, arbitrary precision, interval arithmetic, and mixed precision as separate execution
  backends. Require a backend-specific refinement or error theorem before attributing exact-real guarantees to a
  machine run. See the [arithmetic principle](roadmap/PRINCIPLES.md#18-arithmetic-precision-belongs-to-the-execution-backend).
