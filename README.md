# CFD_Lean

Independent exact-real Lean 4 contracts for compressible CFD. M1 specifies ideal-gas Euler states, conditional primitive/conservative conversion identities, admissibility and physical flux for oriented area vectors in arbitrary finite dimension. See [the contract](specifications/M1.md) and [source/proof map](references/M1.md).

The library imports mathlib only. It does not import SU2, its specifications or implementation. A future SU2 verification package may depend on an immutable CFD_Lean revision. The two projects must use separate working trees and build directories.

## Build and audit

Lean: `leanprover/lean4:v4.19.0`. Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Transitive dependencies are pinned in lake-manifest.json.

With this Lean/Lake toolchain on PATH, run:

```bash
python3 scripts/verify.py
sha256sum -c evidence/SHA256SUMS
```

For an evaluator's source-only build, use a fresh checkout, retain the committed manifest, and do not fetch compiled proof caches. Set `MATHLIB_NO_CACHE_ON_UPDATE=1` for any dependency resolution. No shared `.lake` tree is needed. Proof tactic execution produces terms checked by Lean's kernel; no `native_decide` acceptance shortcut is used.

The initial dependency sources were cloned into independent working trees from already available local Git objects, checked out at the manifest revisions, and assigned their canonical upstream URLs. No dependency build artifacts were copied. The compiler executable is an existing Lean 4.19.0 installation, not a project build directory.

## Review status

The user approved the M1 plan on 2026-11-12. The candidate is not independently accepted. Read the domain limits and foundation policy in specifications/M1.md. Later milestones are Roe flux, node-centered assembly, selected boundary algorithms and explicit time update; none is included in M1.

PDFs stay in the external read-only reference collection. Only bibliography, source locators and mathematical statements in our notation belong in this repository. The user approved the private GitHub repository [rois1995/CFD_Lean](https://github.com/rois1995/CFD_Lean). The initial M1 candidate is frozen by its Git commit; scientific acceptance remains pending.
