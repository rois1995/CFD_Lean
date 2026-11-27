# FVN (FV1D on a non-uniform periodic 1D mesh) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement and bind the eight frozen FVN claims (FVN-U, K, C, A, B, R, M, MB), the three exact controls (FVN-X, FVN-BC, FVN-E) and the trusted challenge for the scalar claims.

**Architecture:** A `Mesh1D` (grid + positive widths) and a generic flux-form update over any real module `S` with a two-point face function `H : S → S → S`. First order and rescaled MUSCL are two face fluxes on that update. Scalar results reuse the existing Harten lemmas `incrementalUpdate_bounds` and `incrementalUpdate_totalVariation_le` unchanged. Burgers and Euler are instances; Euler gets an instance and one control only.

**Tech Stack:** Lean v4.36.0, Mathlib v4.36.0, `scripts/verify.py`, `lake comparator`, GitHub Integration CI.

**Spec:** `specifications/FV1D-nonuniform.md` (frozen at `3eb7cae92331f3107caa942aec4b797577e47d67`), freeze record `specifications/FV1D-nonuniform-approval.md`. Read both before any task.

## Global Constraints

- The frozen contract, approval record and every existing B0–B4, B3b, E0–E0c, FV1D, M1 binding and pin stay byte-identical. Do not edit `Grid`, `FiniteVolume`, `TotalVariation`, `Muscl`, `Limiters`, `Rusanov` (FV1D) or their Burgers/Euler adapters. New code goes in new modules.
- Axioms: only `propext`, `Quot.sound`, `Classical.choice`. No `sorry` at commit time, no raised `maxRecDepth`, no `native_decide`.
- Every Lean run uses the memory cap of `docs/LEAN_PERFORMANCE.md` §6:
  `LEAN_NUM_THREADS=2 systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 nice -n 19 lake env lean <File.lean>`
  (build imports first with the same prefix and `lake build <Module>`; run `lake exe cache get` once in a fresh worktree).
- CI first: after Task 1, push `milestone/fv1d-nonuniform` and open a draft PR into `develop`. No full local `lake build` or `scripts/verify.py` runs. Evidence comes from the CI artifact `regenerated-evidence`.
- Mesh ratio `θ` = `∀ i, θ * max (w i) (w (next i)) ≤ w i + w (next i)`. MUSCL differences are rescaled: `back i = (w i / δ (prev i)) • (U i − U (prev i))`, `fwd i = (w i / δ i) • (U (next i) − U i)`, `δ i = (w i + w (next i)) / 2`. Face states `U i + (1/2) • s i` and `U (next i) − (1/2) • s (next i)`.
- `Mesh1D` stays a fixed periodic 1D mesh. No ALE, AMR or general control-volume interface (freeze record).
- FVN-A is pointwise at one fixed cell. Name it "local affine reconstruction exactness" in the proof map.
- Proof map cites Berger, Aftosmis and Murman, AIAA Paper 2005-0490, and keeps apart "the `SlopeBounded θ` certificate fails for `θ = 2` on stretched cells" from "a limiter cannot be used there".
- Commits end with the session's `Co-Authored-By` and `Claude-Session` lines.

## Review Focus

1. **One-cell grid (`N = 1`).** `next i = prev i = i`; all claims must hold, including FVN-C and FVN-B. Add `example`s on `ZMod 1` in Task 1 and Task 3 that instantiate the public theorems (no extra hypotheses may be needed).
2. **`dt = 0`.** Every step returns its input. The CFL hypotheses are then trivially true; add one `example` per step in Task 1 showing `firstOrderStep m H 0 U = U` and `musclStep m H lim 0 U = U`.
3. **Degenerate bounds `M ≤ m`.** B3 needed `muscl_step_eq_self_of_le` for this case. Task 2 must handle it (state constant ⇒ step is identity), not assume `m < M`.
4. **Wrong-width mutations.** Dividing by the neighbour's width, or using unrescaled differences, must fail a control. Task 4's FVN-BC control pins both (`289/16000` vs `81/4000` vs the unrescaled slope `1/5`).
5. **Seam face.** The face from the last cell to cell 0 uses widths of both cells. The FVN-E control has a non-trivial width at cell 1 and checks cells 0 and 2 against the uniform FV1D values; FVN-BC checks cell 3 (`27/250`), which only sees the seam face.

---

### Task 1: Mesh and generic layer (FVN-U(a), FVN-K, FVN-C, FVN-A)

**Files:**
- Create: `CFDLean/Discrete/Periodic/Mesh1D.lean`
- Create: `CFDLean/Discrete/Periodic/Nonuniform.lean`
- Create (checks): `CFDLean/Discrete/Periodic/NonuniformChecks.lean`
- Modify: `CFDLean.lean` (add the three imports after `CFDLean.Discrete.Periodic.Rusanov`)

**Interfaces:**
- Consumes: `CFDLean.Periodic.Grid` (`next : I ≃ I`, `prev`, `next_prev`, `prev_next`, `sum_prev`), `CFDLean.FV1D.face`, `CFDLean.FV1D.step`.
- Produces (namespace `CFDLean.Periodic`):
  - `structure Mesh1D (I : Type*) where grid : Grid I; width : I → ℝ; width_pos : ∀ i, 0 < width i`
  - `Mesh1D.spacing (m : Mesh1D I) (i : I) : ℝ := (m.width i + m.width (m.grid.next i)) / 2`
  - `Mesh1D.uniform (g : Grid I) (dx : ℝ) (hdx : 0 < dx) : Mesh1D I`
  - `Mesh1D.MeshRatio (m : Mesh1D I) (θ : ℝ) : Prop`
- Produces (namespace `CFDLean.FV1D.Nonuniform`, `variable {S I : Type*} [AddCommGroup S] [Module ℝ S]`):
  - `update (m : Mesh1D I) (dt : ℝ) (h U : I → S) (i : I) : S`
  - `firstOrderStep (m : Mesh1D I) (H : S → S → S) (dt : ℝ) (U : I → S) (i : I) : S`
  - `backDiff fwdDiff (m : Mesh1D I) (U : I → S) (i : I) : S`
  - `slope (m) (lim : S → S → S) (U) (i) : S`, `leftState`, `rightState` (same arguments)
  - `musclStep (m : Mesh1D I) (H lim : S → S → S) (dt : ℝ) (U : I → S) (i : I) : S`
  - `componentwise {n : ℕ} (φ : ℝ → ℝ → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ := fun A B k => φ (A k) (B k)`
  - FVN-C: `update_weighted_sum [Fintype I] (m dt h U) : ∑ i, m.width i • update m dt h U i = ∑ i, m.width i • U i`, plus `firstOrderStep_weighted_sum`, `musclStep_weighted_sum`
  - FVN-K: `firstOrderStep_constant (m H dt C) : firstOrderStep m H dt (fun _ => C) = fun _ => C`; `musclStep_constant (m H lim dt C) (hlim : lim 0 0 = 0)` (same conclusion)
  - FVN-A: `leftState_affine (m lim U i β) (hlim : ∀ d, lim d d = d) (hf : U (m.grid.next i) - U i = m.spacing i • β) (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) : leftState m lim U i = U i + (m.width i / 2) • β`; `rightState_prev_affine` (same hypotheses) `: rightState m lim U (m.grid.prev i) = U i - (m.width i / 2) • β`
  - FVN-U(a): `firstOrderStep_uniform (g F a dx hdx dt U i) : firstOrderStep (Mesh1D.uniform g dx hdx) (FV1D.face F a) dt U i = FV1D.step g F a dx dt U i`

- [ ] **Step 1: Write the checks file first.** `NonuniformChecks.lean` imports `Nonuniform` and contains one `example` per produced theorem, applying it to its own hypotheses, plus the Review Focus items 1–2: `firstOrderStep_weighted_sum` on `Mesh1D (ZMod 1)`, and `firstOrderStep m H 0 U = U`, `musclStep m H lim 0 U = U` (prove these two inline with `funext; simp [firstOrderStep, musclStep, update]`).
- [ ] **Step 2: Run it; expect failure** — `unknown identifier` / `unknown namespace`.
- [ ] **Step 3: Implement `Mesh1D.lean` and `Nonuniform.lean`.** `update` is `U i - (dt / m.width i) • (h i - h (m.grid.prev i))`. FVN-C: `m.width i • (dt / m.width i) • x = dt • x` by `width_pos`, then reindex with `Grid.sum_prev` as in `FV1D.step_sum`. FVN-U(a) unfolds to `FV1D.step` (expect `rfl` or `simp`). FVN-A: both rescaled differences become `m.width i • β` because `m.width i / δ * δ = m.width i` (`δ > 0`).
- [ ] **Step 4: Run the checks file under the memory cap; expect no errors and no `sorry` warning.**
- [ ] **Step 5: Commit, push, open a draft PR into `develop`** titled "Implement FV1D on a non-uniform periodic mesh (FVN)". Body: milestone FVN, link the contract, "implementation in progress".

### Task 2: Scalar MUSCL on the mesh (FVN-R, FVN-M)

**Files:**
- Create: `CFDLean/Discrete/Periodic/NonuniformMuscl.lean` (namespace `CFDLean.FV1D.Nonuniform`)
- Modify: `CFDLean/Discrete/Periodic/NonuniformChecks.lean`, `CFDLean.lean`

**Interfaces:**
- Consumes: Task 1; `CFDLean.Scalar.FiniteVolume.{SlopeBounded, incrementalUpdate, incrementalUpdate_bounds, incrementalUpdate_totalVariation_le, totalVariation, boundedStates, boundedStates_convex}`; `CFDLean.Scalar.{NumericalFlux, MonotoneFlux, LipschitzOnBounds}`.
- Produces (all with `(m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ) (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi)`):
  - FVN-R: `leftState_mem … (i) : lo ≤ leftState m φ u i ∧ leftState m φ u i ≤ hi`, `rightState_mem` (same shape)
  - FVN-M(a): `musclStep_mem … (nf : NumericalFlux) (hmono : MonotoneFlux nf) (KL KR : ℝ) (hlip : LipschitzOnBounds nf lo hi KL KR) (dt : ℝ) (hdt : 0 ≤ dt) (hcfl : ∀ i, dt * ((KL + KR) / m.width i + θ * (KR / (m.width i + m.width (m.grid.next i)) + KL / (m.width (m.grid.prev i) + m.width i))) ≤ 1) : musclStep m nf.eval φ dt u ∈ boundedStates lo hi`
  - FVN-M(b): `musclStep_totalVariation_le [Fintype I] …` same, with `hcfl : ∀ i, dt * (KR / m.width i + KL / m.width (m.grid.next i) + θ * (KL + KR) / (m.width i + m.width (m.grid.next i))) ≤ 1`, conclusion `totalVariation m.grid (musclStep m nf.eval φ dt u) ≤ totalVariation m.grid u`
  - Helper exported for Task 3: `musclStep_incremental` giving `C D : I → ℝ` with `0 ≤ C i ≤ dt / m.width i * KR * (1 + θ * p i)` and `0 ≤ D i ≤ dt / m.width (m.grid.next i) * KL * (1 + θ * q i)`, where `p i = m.width i / (m.width i + m.width (next i))`, `q i = m.width (next i) / (m.width i + m.width (next i))`, and `musclStep … = incrementalUpdate m.grid C D u`.

- [ ] **Step 1: Add `example`s to the checks file** for the four public theorems, plus Review Focus 3: an `example` with `hi ≤ lo` that applies `musclStep_mem` (no `lo < hi` premise is allowed in the public statements).
- [ ] **Step 2: Run the checks file; expect `unknown identifier`.**
- [ ] **Step 3: Implement.** Follow the B3b proof shape in `Limiters.lean` (`half_slope_mem_two`, `slope_combo_bounded`, `*_sub_bounded`, `flux_*_increment_bounded`, `coeff_sum_le_one_bounded`), replacing the constants `1/2` by `p i`, `q i`. Key bounds: `|s i / 2| ≤ θ * p i * |Δ i|` against the forward difference and `≤ θ * q (prev i) * |Δ (prev i)|` against the backward one; jump ratios in `[1 − θ p (prev i), 1 + θ q (prev i)]` (left states) and `[1 − θ q i, 1 + θ p i]` (right states); MeshRatio gives `θ p i ≤ 1` and `θ q i ≤ 1`. Degenerate `hi ≤ lo`: show `u` is constant and use `musclStep_constant` (with `φ 0 0 = 0`, which follows from `SlopeBounded`).
- [ ] **Step 4: Run the checks file; expect no errors, no `sorry`.**
- [ ] **Step 5: Commit and push.**

### Task 3: Burgers instance (FVN-U(b), FVN-B, FVN-MB)

**Files:**
- Create: `CFDLean/Schemes/Burgers/Nonuniform.lean` (namespace `CFDLean.Burgers.Nonuniform`)
- Modify: `CFDLean/Discrete/Periodic/NonuniformChecks.lean` (or a Burgers checks section), `CFDLean.lean`

**Interfaces:**
- Consumes: Tasks 1–2; `CFDLean.Burgers.{physicalFlux, Rusanov.waveSpeed, Rusanov.numericalFlux, Rusanov.eval, fv1d_face_eq, Rusanov.lipschitzOnBounds, Rusanov.musclEulerStep}`, `Time.SSP.{ssprk2, ssprk3, iterate_mem, iterate_le, ssprk2_mem, ssprk3_mem, ssprk2_le, ssprk3_le}`, `totalVariation_convexOn`.
- Produces:
  - `face : ℝ → ℝ → ℝ := FV1D.face physicalFlux Rusanov.waveSpeed`
  - `firstOrderStep (m : Mesh1D I) (dt : ℝ) : (I → ℝ) → I → ℝ`, `musclStep (m) (dt) (φ) : (I → ℝ) → I → ℝ`, `musclSsprk2Step`, `musclSsprk3Step` (via `Time.SSP.ssprk2/3 (musclStep m dt φ)`)
  - FVN-U(b): `musclStep_uniform (g dx hdx dt φ u i) : musclStep (Mesh1D.uniform g dx hdx) dt φ u i = Rusanov.musclEulerStep g dx dt φ u i`
  - FVN-B: with `a i = Rusanov.waveSpeed (u i) (u (m.grid.next i))`: `firstOrderStep_mem (m dt) (hdt : 0 ≤ dt) (lo hi u) (hu) (hcfl : ∀ i, dt * (a (m.grid.prev i) + a i) ≤ m.width i) : firstOrderStep m dt u ∈ boundedStates lo hi`; `firstOrderStep_totalVariation_le [Fintype I] (m dt) (hdt) (u) (hcfl : ∀ i, dt * a i ≤ min (m.width i) (m.width (m.grid.next i))) : totalVariation m.grid (firstOrderStep m dt u) ≤ totalVariation m.grid u`
  - FVN-MB: `musclStep_iterate_stable`, `musclSsprk2Step_iterate_stable`, `musclSsprk3Step_iterate_stable`, each `[Fintype I] (m dt lo hi φ θ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ m.width i) (u) (hu : u ∈ boundedStates lo hi) (n : ℕ)` concluding bounds and TV for `(step)^[n] u`, as `Rusanov.musclEulerStep_iterate_stable_bounded`. (`n` steps imply the contract's one SSPRK step at `n = 1`.)

- [ ] **Step 1: Add checks** for every produced theorem; Review Focus 1: `firstOrderStep_totalVariation_le` on `Mesh1D (ZMod 1)`.
- [ ] **Step 2: Run; expect `unknown identifier`.**
- [ ] **Step 3: Implement.** FVN-U(b): `fv1d_face_eq` (funext) then unfold to `musclRhs`; the rescale factors are `dx / dx = 1`. FVN-B: incremental form with `C i = dt / m.width i * ((a i − mean i) / 2)`, `D i = dt / m.width (next i) * ((a i + mean i) / 2)`, `mean i = (u i + u (next i)) / 2`, `|mean i| ≤ a i` (`abs_mean_le_waveSpeed`); TV uses `C i + D i ≤ dt * a i / min(…)`. FVN-MB: from Task 2 with `KL = KR = 2 * max |lo| |hi|`, using `θ p i ≤ 1`, `θ q i ≤ 1` and `θ * 2K / (w i + w (next i)) ≤ K / w i + K / w (next i)`; then copy the SSP wiring of `RusanovLimiters.lean`.
- [ ] **Step 4: Run checks; expect clean.**
- [ ] **Step 5: Commit and push.**

### Task 4: Exact controls (FVN-X, FVN-BC, FVN-E) and the Euler instance

**Files:**
- Create: `CFDLean/Schemes/Burgers/NonuniformControls.lean`
- Create: `CFDLean/Schemes/Euler/Nonuniform.lean` (namespace `CFDLean.Euler1D`)
- Create: `CFDLean/Schemes/Euler/NonuniformControls.lean`
- Modify: `CFDLean.lean`

**Interfaces:**
- Consumes: Tasks 1–3; `CFDLean.Euler1D.{encode, decode, flux, speed}`; `CFDLean.Scalar.FiniteVolume.{minmod, limitedSlope, mcFactor, superbeeFactor, vanLeerFactor, vanAlbadaFactor, centralSlope, slope}`; the `sqrt` value lemmas of `CFDLean/Schemes/Euler/FV1DControls.lean`.
- Produces:
  - `Euler1D.nonuniformStep (γ : ℝ) (m : Mesh1D I) (dt : ℝ) (U : I → Conservative 1) (i : I) : Conservative 1 := decode (Nonuniform.firstOrderStep m (FV1D.face (flux γ) (speed γ)) dt (fun j => encode (U j)) i)`
  - `Euler1D.musclLeft / musclRight (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (U : I → Conservative 1) (i : I) : Conservative 1` via `decode (Nonuniform.leftState m (componentwise φ) (fun j => encode (U j)) i)`
  - `Burgers.Nonuniform.meshRatio_needed` (FVN-X theorem, bound under FVN-R in Task 6)

Control data (exact; all from the frozen contract):
- `m4 : Mesh1D (ZMod 4)`: `zmodGrid 4`, widths `![1, 3, 1, 1]`; `u4 = ![0, 1, 6/5, 0]`.
- `m3 : Mesh1D (ZMod 3)`: `zmodGrid 3`, widths `![1, 2, 1]`; Euler states `(ρ, ρ, 2 + ρ/2)` for `ρ = 1, 4, 9`, `γ = 2`.

- [ ] **Step 1: Write the controls as theorem statements with `:= by sorry`:**
  - FVN-X `meshRatio_needed`: `leftState m4 φ u4 1` equals `23/20` (`minmod`), `61/52` (`limitedSlope vanAlbadaFactor`), `5/4` (`limitedSlope vanLeerFactor`), `13/10` (`limitedSlope mcFactor`, `limitedSlope superbeeFactor`), `29/20` (`centralSlope`); `u4 ∈ boundedStates 0 (6/5)`; `m4.MeshRatio (5/4)` and `¬ m4.MeshRatio 2`.
  - FVN-BC: `firstOrderStep m4 (1/10) u4 = ![1/40, 1463/1500, 1141/1000, 27/250]`; `musclStep m4 (1/10) minmod u4 = ![289/16000, 23327/24000, 18529/16000, 27/250]`; both `∑ i, m4.width i * _ = 21/5`; `Nonuniform.slope m4 minmod u4 1 = 3/10` while `FiniteVolume.slope (zmodGrid 4) minmod u4 1 = 1/5`; `Nonuniform.update m4 (1/10) (FiniteVolume.musclFlux (zmodGrid 4) Rusanov.numericalFlux minmod u4) u4 0 = 81/4000` (the unrescaled B3 face states on the same widths).
  - FVN-E: `nonuniformStep 2 m3 (1/16) U` has densities `(35/16, 249/64, 257/32)`, momenta equal to densities, energies `(99/32, 505/128, 385/64)`; width-weighted totals `18, 18, 17` before and after; `musclLeft m3 minmod U` = `(1,1,5/2), (6,6,5), (9,9,13/2)` and `musclRight` = `(2,2,3), (9,9,13/2), (1,1,5/2)`.
- [ ] **Step 2: Run each controls file; expect only `declaration uses 'sorry'` warnings.**
- [ ] **Step 3: Prove them** with `simp`/`norm_num` on `Fin`/`ZMod` cases (`fin_cases`, `decide` only on `ZMod` index facts). No `native_decide`.
- [ ] **Step 4: Run; expect clean.**
- [ ] **Step 5: Commit and push.**

### Task 5: Trusted challenge for the scalar claims

**Files:**
- Create: `CFDLean/Verification/FV1DNonuniformChallenge.lean` (imports only `Mathlib.*`)
- Create: `CFDLean/Verification/FV1DNonuniformVerify.lean` (bridges)
- Create: `Challenges/FV1DNonuniform.lean`, `Challenges/FV1DNonuniform.comparator.json`
- Create: `reviews/FVN/TrustedStatements_Review.md`
- Modify: `KernelAudit.lean` (import the Verify module, as for `BurgersB3bVerify`), `lakefile.toml` if B3b's challenge needed an entry there

**Interfaces:**
- Consumes: Tasks 2–4 public theorems.
- Produces trusted `Prop` definitions (names fixed here; each restates its claim with Mathlib-only definitions — mesh as `next : I ≃ I` plus `w : I → ℝ` with `∀ i, 0 < w i`, the rescaled reconstruction, the update, Rusanov Burgers, `SlopeBounded`, monotone and Lipschitz flux — adapting `BurgersB3bChallenge.lean`):
  `FirstOrderBounds I`, `FirstOrderTotalVariation I` (FVN-B), `ReconstructionBounds I` (FVN-R), `MusclBounds I`, `MusclTotalVariation I` (FVN-M), `MusclEulerMultiStep I`, `MusclSSPRK2MultiStep I`, `MusclSSPRK3MultiStep I` (FVN-MB), `MeshRatioOvershoot` (FVN-X, under FVN-R). Bridges in `CFDLean.Verification.FV1DNonuniformVerify` with snake_case names (`first_order_bounds`, …, `mesh_ratio_overshoot`); 9 bridges.

- [ ] **Step 1: Write the statements module and the challenge file** (`theorem <bridge> : <Statement> := sorry`, same layout as `Challenges/BurgersB3b.lean`) and the config (`permitted_axioms` exactly `propext`, `Quot.sound`, `Classical.choice`; `definition_names` empty).
- [ ] **Step 2: Write the bridges**; each bridge proves its statement and directly uses the promised theorem of its ID. Run the Verify module; expect clean.
- [ ] **Step 3: AI statement review.** Dispatch a fresh reviewer with the contract and the statements file only; it checks each `Prop` against the frozen claim (quantifiers, CFL forms, mesh ratio, face orientation, seam). Record the verdict verbatim in `reviews/FVN/TrustedStatements_Review.md`. Fix and re-review until no mandatory finding.
- [ ] **Step 4: Commit and push; add the `paranoid` label to the PR** to run the sandboxed comparator. Expected: the FVN challenge passes.

### Task 6: Registration, evidence and handoff

**Files:**
- Create: `specifications/FV1D-nonuniform-results.json` (format of `Burgers-B3b-results.json`: `contract`, `contract_sha256`, `approval_record`, `approved_revision = 3eb7cae92331f3107caa942aec4b797577e47d67`, `source_map`, `trusted_statement_review`, `independent_acceptance = "pending"`, `results`, `modules`, `trusted`)
- Create: `references/FV1D-nonuniform.md` (proof map, one row per ID, local-affine wording, Berger–Aftosmis–Murman citation, controls)
- Create: `reviews/FVN/Reviewer_Prompt.md` (revision-pinned handoff, as `reviews/FV1D/Reviewer_Prompt.md`)
- Modify: `scripts/verify.py` (`BURGERS["FVN"]` entry with results path, approved revision, statements/challenge paths and hashes, `count`, `bridges = 9`; `CATALOG_STATUS["FVN"] = "pending"`), `scripts/catalog.py` (`MILESTONES` += `"FVN"`; rules text), `scripts/test_verify.py` (only if a fixture counts milestones explicitly), `catalog/theorems.json` (one entry per promised theorem, `milestone: "FVN"`, `status: "pending"`, `source: "references/FV1D-nonuniform.md"`), `catalog/README.md` (regenerate), `StatementChecks.lean` (one `example` per public claim, as the FV1D section), `roadmap/CURRENT.md`, `roadmap/NEXT.md`, evidence files (from CI).

- [ ] **Step 1: Write the result map and verifier entry.** `count` = number of `declarations` across the eight IDs. Results: FVN-U (`firstOrderStep_uniform`, `Burgers.Nonuniform.musclStep_uniform`), FVN-K, FVN-C, FVN-A (Task 1), FVN-B, FVN-MB (Task 3), FVN-R (Task 2 + `meshRatio_needed`), FVN-M (Task 2). Definitions bound under the ID that introduces them.
- [ ] **Step 2: Run `python3 -m unittest discover -s scripts -p test_verify.py` and `python3 scripts/catalog.py --check`** (no Lean). Expected: pass, or only failures that need regenerated evidence.
- [ ] **Step 3: Push. Let Integration CI run.** If the verifier or evidence comparison fails only for evidence, download `regenerated-evidence`, check that the diff touches only FVN rows plus the new `RAW_TYPES_SHA256`, commit it, push. Expected final CI: green.
- [ ] **Step 4: Run link, whitespace and checksum checks** (`git diff --check`; every relative link in the new Markdown resolves).
- [ ] **Step 5: Write the reviewer prompt** pinned to the green candidate commit; update the PR body (milestone, what changed, checks, pending review) and mark the PR ready.
