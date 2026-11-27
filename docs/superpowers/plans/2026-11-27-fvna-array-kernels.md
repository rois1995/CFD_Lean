# FVNA (executable kernels on the non-uniform mesh) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Implement and bind FVNA-F, FVNA-M, FVNA-U, FVNA-T, the controls and the trusted challenge.

**Architecture:** New executable kernels in `CFDLean/Exec/` that take `widths : Array α`; real-arithmetic refinement to
the FVN steps (`CFDLean.FV1D.Nonuniform`, `CFDLean.Burgers.Nonuniform`, `CFDLean.Euler1D.nonuniformStep`); FVN
guarantees transferred to arrays, as E0b/E0c did for B3/B3b.

**Spec:** `specifications/FV1D-nonuniform-array.md` (frozen at `d0c5298`), approval
`specifications/FV1D-nonuniform-array-approval.md`, review records `reviews/FVNA/`. Branch is built on FVN (#43); the
FVN code, its Burgers/Euler instances and controls are available and must not be edited.

## Global Constraints

- Do not edit any existing module (Kernel, MusclKernel, LimiterKernel, FV1D, *Refinement, FVN modules, Main.lean) or
  any frozen spec. New code only in new modules.
- Kernel formulas exactly as the contract ("Kernels"): first order reuses `Exec.FV1D.Model`/`face`; MUSCL reuses
  `limiterSlope` and `rusanov`; rescaling `two * w[i] / (w[i−1] + w[i])` and `two * w[i] / (w[i] + w[i+1])`; update
  divides by `w[i]`; SSPRK2/3 via `axpby` as in LimiterKernel. Only existing `Scalar`/`ScalarSign` operations.
- Widths read with a total accessor (e.g. `widths.getD i Scalar.one`-style default; implementer picks a default the
  `Scalar` class supplies); theorems assume `widths.size = u.size = n ≥ 1` and positive widths.
- FVNA-F binds only the concrete Burgers and Euler real models; the generic stencil lemma is for the compatible model
  `⟨(· + ·), (· - ·), (· • ·), F, a⟩` and is supporting. One explicit face/width alignment lemma (seam included).
- FVNA-T (b), (c) use `EntriesBetween m M u`; (c) has `L ≠ .none`, mesh ratio `L.theta` on `mesh widths`, `0 ≤ dt`,
  `8 * dt * max |m| |M| ≤ w[i]`.
- Owner rules: follow docs/LEAN_PERFORMANCE.md (capped runs `LEAN_NUM_THREADS=2 systemd-run --user --scope -q -p
  MemoryMax=16G -p MemorySwapMax=0 nice -n 19 lake env lean <File>`, one at a time, timed; no native_decide; no raised
  maxRecDepth; controls in their own module, one value per declaration). CI first: no full build, no full verifier.
- Commits end with the session Co-Authored-By / Claude-Session lines.

## Review Focus
1. `n = 1` (seam reads itself) and `dt = 0` (identity) for every kernel.
2. Width/state index alignment at the seam (the alignment lemma; the FVN-BC control detects a wrong pairing).
3. Empty input: empty output, no indexing (executable check, outside theorems).
4. Uniform widths over ℝ reduce rescaling to exactly 1 (FVNA-U) for every limiter, no limiter case split.
5. Initial bounds hypothesis present in every transferred bounds statement.

---

### Task 1: Kernels
Files: create `CFDLean/Exec/NonuniformKernel.lean`; modify `CFDLean.lean`.
Produces (namespace `CFDLean.Exec`): `FV1D.nonuniformStepArray (M : FV1D.Model α S) (half dt : α) (widths : Array α) (old : Array S) : Array S`;
`nuLimiterEulerStepArray (L : Limiter) (dt : α) (widths u : Array α) : Array α`, `nuLimiterSsprk2StepArray`, `nuLimiterSsprk3StepArray` (same arguments);
`size_*` simp lemmas. Steps: write the kernels; a checks section with `#eval` on small `Float` inputs (empty, one cell, FVN-BC data) printing results; capped run clean; commit.

### Task 2: Refinement (FVNA-F, FVNA-M, FVNA-U)
Files: create `CFDLean/Exec/NonuniformRefinement.lean`. Uses `Represents`, `samples`, `samples_entries` patterns of
`Refinement.lean`/`FV1DRefinement.lean`. Produces: `meshOf (widths : Array ℝ) (h…) : Periodic.Mesh1D (ZMod n)` (or
equivalent) and the alignment lemma; FVNA-F `burgers_nonuniform_refines`, `euler_nonuniform_refines`; FVNA-M
`nuLimiterEulerStepArray_refines`, `nuLimiterSsprk2StepArray_refines`, `nuLimiterSsprk3StepArray_refines`; FVNA-U
`nonuniformStepArray_uniform`, `nuLimiter*StepArray_uniform` (three). Steps: statements with sorry → prove → capped
run → commit.

### Task 3: Transfer (FVNA-T)
Files: create `CFDLean/Exec/NonuniformTransfer.lean`. Produces: (a) Burgers weighted sum kept by every kernel, Euler
componentwise weighted sums kept by the first-order kernel; (b) first-order Burgers bounds (with `EntriesBetween`)
and TV; (c) `n`-step FE/SSPRK2/SSPRK3 bounds and TV for `L ≠ .none` under the FVN-MB hypotheses. Proofs transfer FVN
theorems through Task 2 refinement. Steps: statements → proofs → capped run → commit.

### Task 4: Controls
Files: create `CFDLean/Exec/NonuniformControls.lean`. Real-array exact values from the contract "Controls" (Burgers
first order and minmod MUSCL on FVN-BC data; Euler first order on FVN-E data), one value per declaration; `n = 1`,
`dt = 0` instances; empty input. Steps: sorry stage → prove → capped run → commit.

### Task 5: Trusted challenge
Files: `CFDLean/Verification/FV1DNonuniformArrayChallenge.lean` (imports Mathlib + hash-pinned
`trusted_inputs`: the kernel modules it needs, as E0c), `CFDLean/Verification/FV1DNonuniformArrayVerify.lean`,
`Challenges/FV1DNonuniformArray.lean`, `.comparator.json`; `KernelAudit.lean` import. Covers FVNA-M and FVNA-T.
Measure `con-ron`/`con-leche` (rule 9). Controller runs the AI statement review.

### Task 6: Registration
`specifications/FV1D-nonuniform-array-results.json`, `scripts/verify.py` BURGERS["FVNA"] (pending, own bridge key,
trusted_inputs), catalog, StatementChecks, proof map `references/FV1D-nonuniform-array.md`, CI `--wfail` lists,
roadmap. Evidence and raw-types pin from CI (controller).
