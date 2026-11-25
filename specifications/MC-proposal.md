# MC proposal: Lean v4.36.0 and the numerical core library

Status: proposal and candidate implementation on the local branch `core-v436` (not pushed). Written 2026-11-25 under
the standing implementation authorization (`reviews/Standing_Authorization.md`) and the user's message in the
JST_Paper_Lean session: "Go on, report when finished and we can push the CFD_Lean updates." Independent acceptance
remains with the reviewer. No accepted result is re-accepted by this document.

## 1. Why

- Move from `leanprover/lean4:v4.19.0` + Mathlib `c44e0c8` to `leanprover/lean4:v4.36.0` + Mathlib tag `v4.36.0`
  (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). Newer Lean ships the proof-validation tooling (`lake comparator`,
  multiple independent kernels) recommended for "the proof is checked in Lean" claims.
- Make CFD_Lean the main core library: add the generic, paper-independent blocks proved in JST_Paper_Lean
  (`NumCore`), so downstream projects (JST paper 1 and later papers) import one core.
- Add a theorem catalog: every promised theorem with its layer and method tags (FEM / FVM / both / method-free).

## 2. Scope

### MC-T (toolchain port, no new mathematics)

- Port every CFD_Lean source to v4.36.0 / Mathlib v4.36.0. Allowed changes: renamed or removed Mathlib lemmas and
  notations, tactic behaviour changes, elaboration fixes. Not allowed: changing any definition's meaning or any
  promised statement beyond the mechanical renames required by the new library.
- All 199 promised bindings (156 accepted M1-M4, 43 M5 pending review) keep their IDs, names and stages.
- Evidence: for every promised theorem, the v4.19 accepted type string and the v4.36 type string side by side
  (`evidence/port-types.json`), with every difference classified (Mathlib rename / notation / pretty-printer only /
  other). "Other" must be empty. Every accepted source file gets a diff against its accepted revision
  (`evidence/port-sources.patch`).
- The verifier's accepted-source hash and exact-type guards are re-based: they compare against the v4.19 accepted
  evidence through the reviewed type map above, and against the new MC candidate for future milestones.

### MC-N (numerical core, new modules, no change to M1-M5)

New namespace `CFDLean.Num` (modules under `CFDLean/Num/`), ported from JST_Paper_Lean `NumCore` and its generic
proofs: vectors and pair sums; log mean; P1 simplex calculus (gradients, facets, volumes, facet = cross product in
3D, rotated edge in 2D); weighted simplex meshes with their P1 operators (SBP form and defect, facet pairing, facet
balance, boundary facets); entropy-conservative two-point fluxes (Tadmor) and pair productions; Galerkin ⇔
finite-volume identity; boundary quadrature closure; Loewner order of dissipation tensors. Each module keeps its
theorems' statements as proved in JST_Paper_Lean (renamed namespace). A bridge module relates `CFDLean.Num` simplex
meshes and the M3 median dual (the JST `CFDBridge` results).

### MC-C (catalog)

`catalog/theorems.json` and a generated `catalog/README.md`: for every promised theorem its ID, Lean name, layer
(Foundations / Geometry / Discrete operators / Entropy framework / Physics models / Schemes), method tags, source
reference and status (accepted / pending / candidate). The verifier checks that the catalog covers exactly the
promised theorems.

## 3. Not in scope

Folding the JST paper-1 formalization into this repository (planned later, separate milestone); new physics; any
change to the M5 contract or its pending review; making the repository public.

## 4. Verification

`python3 scripts/verify.py` (re-based guards), the fixtures, `KernelAudit.lean` (standard axioms only), and, if the
v4.36 toolchain provides it, `lake comparator --paranoid` on all promised theorems. A fresh source-only replay script
updated for v4.36.

## 5. Review requests

The reviewer is asked to check: (1) the type map has no "other" differences; (2) no definition changed meaning; (3)
`CFDLean.Num` adds no axiom and does not alter M1-M5; (4) catalog coverage; (5) replay.
