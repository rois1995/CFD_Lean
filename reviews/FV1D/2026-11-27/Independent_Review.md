# Independent review of all open CFD_Lean pull requests

**Repository:** `rois1995/CFD_Lean`  
**Review date:** 2026-11-27  
**Scope:** all open PRs at the time of review, PR #50 through PR #65.  
**Review policy:** proposal/roadmap PRs are judged as scope/design artifacts; implementation PRs are judged against the repository's frozen-scope, exact-real refinement, trust-boundary, and CI conventions.

## Executive summary

| PR | Short verdict |
|---|---|
| #50 | **ACCEPT ROADMAP CLARIFICATION** |
| #51 | **RECOMMEND FREEZING E1 PROPOSAL** |
| #52 | **SOURCE-LEVEL PASS; conditional on #51 freeze** |
| #53 | **SOURCE-LEVEL PASS; conditional on #51 freeze** |
| #54 | **SOURCE-LEVEL PASS; conditional on #51 freeze** |
| #55 | **SOURCE-LEVEL CONTROL PASS; native-boundary evidence should be strengthened later** |
| #56 | **RECOMMEND FREEZING EULER MUSCL TRACE PROPOSAL** |
| #57 | **SOURCE-LEVEL PASS; conditional on #56 freeze** |
| #58 | **RECOMMEND FREEZING 2D ORIENTED-FACE PROPOSAL; controls pass** |
| #59 | **ACCEPT RECONSTRUCTION-INTERFACE PLAN** |
| #60 | **REQUEST CHANGES: scientific scope/result binding not yet frozen** |
| #61 | **ACCEPT SEQUENCING PLAN** |
| #62 | **REQUEST CHANGES: graded-WENO scientific proof gap + stack/base issue + CI pending** |
| #63 | **REQUEST CHANGES: full SSPRK3 refinement missing + stack/base issue + CI pending** |
| #64 | **REQUEST CHANGES: Euler reconstruction scope/refinement/timestep issues + stack/base issue** |
| #65 | **REGRESSION IMPLEMENTATION LOOKS SOUND, but acceptance blocked by upstream #64 and stack/base state** |

A recurring process issue begins at #60: the repository is moving production mathematical/numerical code faster than it is freezing the corresponding scientific contracts. The code is often technically good, but the current repository workflow has intentionally separated **proposal freeze** from **implementation acceptance**. I recommend preserving that discipline for the WENO and Euler-reconstruction line.

A second issue begins at #62: PRs #62–#65 currently target `develop` while their commits form a dependency chain. As currently based, each PR contains substantial unaccepted predecessor work. They should be retargeted to their immediate predecessor branch for incremental review/merge, or held until all predecessors are accepted and merged and then rebased onto `develop`.

---

# PR #50 — Clarify prerequisites for E1, reconstruction and fixed-mesh 2D work

**Reviewed head:** `03adbe733ec856271b90134e2d832bbb8dc77b7b`  
**Base:** `3a3dbc26a42128822c5a274edaa0ee888b5c8411`  
**CI:** Integration CI passed.

### Mandatory changes

None.

The sequencing is technically sensible. A one-step first-order Burgers binary64 contract is a good first E1 target because the exact-real kernel/refinement pair already exists and the reconstruction, geometry and time-composition questions can remain outside that first arithmetic milestone.

The roadmap also correctly keeps exact-real fixed-mesh 2D work independent of E1 and preserves the previously agreed reconstruction trigger: do not create a universal reconstruction abstraction from MUSCL alone; extract it when a structurally different second family exists.

### Non-blocking suggestions

Keep the distinction between “recommended next task” and “hard dependency” prominent. The text already says the 2D geometry work can proceed independently; that is important because E1 should not become an artificial gate on exact-real numerical development.

The roadmap still contains some status prose inherited from earlier revisions that may become stale as accepted PRs land. That is general maintenance, not a defect in this PR's changed sequencing.

### Independent external reviewer conclusion

**ACCEPT ROADMAP CLARIFICATION** at `03adbe733ec856271b90134e2d832bbb8dc77b7b`.

The prerequisite ordering is compatible with the repository architecture and with the earlier decision to defer a general reconstruction interface until a second reconstruction family creates real abstraction pressure.

---

# PR #51 — Propose a one-step E1 binary64 budget and eight-step review queue

**Reviewed head:** `4b914b5bb3ea39ded55b958f5b29d72b7bd20c80`  
**Base:** `03adbe733ec856271b90134e2d832bbb8dc77b7b`  
**CI:** no dedicated workflow run on this individual stacked head; the cumulative stack through PR #58 passed Integration CI.

### Mandatory changes

None.

The proposed E1 scope is appropriately narrow and honest. It certifies an **a posteriori**, per-input absolute error bound for one observed first-order Forward Euler step, rather than claiming an a priori floating-point theorem for all inputs or a certified SSPRK3 run.

The reference is correctly fixed to the same arithmetic association and periodic stencil as the existing kernel. The proposal also correctly separates:

- exact interpretation of finite binary64 inputs;
- exact rational replay;
- real-kernel correspondence;
- the logical `Float` result;
- and the additional trust assumption needed for native compiled execution.

That separation is exactly what the repository's arithmetic-backend principle requires.

### Non-blocking suggestions

The phrase that the caller chooses the budget “before the comparison” is procedural rather than something the Lean theorem can enforce. The eventual certificate should be described as proving the bound for the supplied budget; any precommitment policy belongs to provenance/workflow metadata.

For a later native-run certificate, record the compiled binary/toolchain identity and the recovered output bits in run provenance. That is outside this proposal but follows naturally from its trust-boundary wording.

### Independent external reviewer conclusion

**RECOMMEND FREEZING THE E1 ONE-STEP PROPOSAL AS WRITTEN** at `4b914b5bb3ea39ded55b958f5b29d72b7bd20c80`.

The scope is useful, falsifiable, reviewable, and avoids silently promoting one-step binary64 evidence into a claim about SSPRK3, Euler, reconstruction, analytic initial-data error, or arbitrary native execution.

---

# PR #52 — Decode finite binary64 values exactly for E1 reference checks

**Reviewed head:** `e6b6cf620e8e0395f52a06e7d37efd27c2937ea7`  
**Base:** `4b914b5bb3ea39ded55b958f5b29d72b7bd20c80`

### Mandatory changes

None in the draft implementation.

The decoder maps `Float.Model.UnpackedFloat` finite values to the signed dyadic `mantissa * 2^exponent`, maps both signed zeros to rational zero, and rejects infinities/NaNs. The classification theorem `value_isSome` exactly matches `Float.isFinite`.

The bit-pattern controls cover the important semantic edges: both zeros, the least subnormal, the least normal, a negative normal value, the largest finite binary64 value, infinity and NaN.

Final milestone acceptance should still wait for the E1 proposal in #51 to be frozen and for this draft to be promoted into the repository's normal result-binding/trust workflow.

### Non-blocking suggestions

When this leaves `ReviewCases`, add a short traceability note that pins the exact Lean `Float.Model` source revision whose `unpack` field meanings are being used. The toolchain pin already gives the dependency implicitly, but the arithmetic certificate will benefit from an explicit source pointer.

A round-trip or model-semantics lemma can be added if the production E1 contract needs one; the current structural definition and controls are sufficient feasibility evidence.

### Independent external reviewer conclusion

**SOURCE-LEVEL PASS** at `e6b6cf620e8e0395f52a06e7d37efd27c2937ea7`.

The finite-value interpretation is consistent with the pinned binary64 model and is a suitable basis for the proposed E1 exact replay. Final implementation acceptance is conditional on #51's scope freeze and normal production binding/evidence.

---

# PR #53 — Prove rational Burgers replay agrees with the real array kernel

**Reviewed head:** `58ac2022ff274a056df18180eecb14675f03a2b1`  
**Base:** `e6b6cf620e8e0395f52a06e7d37efd27c2937ea7`

### Mandatory changes

None.

The rational `Scalar` instance matches the kernel operations, `cast_face` correctly transports the Burgers Rusanov flux through `ℚ -> ℝ`, including `abs` and `max`, and `cast_step` proves equality for the entire periodic array rather than for an informal replacement stencil.

This is the right proof direction: reuse the actual kernel, then compose with the already accepted real refinement.

### Non-blocking suggestions

An explicit singleton or seam example would be a useful regression, but the theorem already quantifies over the whole array and unfolds the actual periodic indexing, so this is not needed for correctness.

Keep this theorem about the exact kernel expression; do not refactor it into a mathematically equivalent but differently associated stencil, because E1 is specifically sensitive to operation association.

### Independent external reviewer conclusion

**SOURCE-LEVEL PASS** at `58ac2022ff274a056df18180eecb14675f03a2b1`.

The rational replay is correctly tied to the exact real array kernel and provides the reference bridge needed by the E1 checker.

---

# PR #54 — Check a per-cell binary64 budget and prove real-step soundness

**Reviewed head:** `a53c21ff9fc74718f207e3446857fc5a276ed0e5`  
**Base:** `58ac2022ff274a056df18180eecb14675f03a2b1`

### Mandatory changes

None.

`checkStep` is fail-closed on non-finite inputs, empty state, non-positive `dx`, negative `dt`, and negative budgets. It calls the existing Float kernel directly and compares it against the exact rational evaluation of the same kernel.

`checkStep_sound` covers every reference cell, proves the observed cell decodes to a finite rational, and gives the requested absolute bound. `real_cell_bound` then states the inequality directly against the real kernel by composing with the rational-to-real step theorem.

The result is intentionally a checker-soundness theorem rather than an analytic floating-point bound, which matches #51.

### Non-blocking suggestions

Keep the logical/native distinction explicit when this moves into production. The theorem certifies the logical `Float` result represented in Lean; it does not by itself certify a separately compiled executable unless the native trust assumption is attached.

A future certificate structure may want to retain the exact rational reference and measured maximum error as data, not merely the Boolean acceptance result.

### Independent external reviewer conclusion

**SOURCE-LEVEL PASS** at `a53c21ff9fc74718f207e3446857fc5a276ed0e5`.

The quantifiers, rejection paths, array-size coverage and reference association are sound for the proposed a posteriori E1 milestone.

---

# PR #55 — Exercise E1 rounding, underflow, overflow and rejection controls in CI

**Reviewed head:** `8549497734c05c6b29b0257bc0f5450b5bbef404`  
**Base:** `a53c21ff9fc74718f207e3446857fc5a276ed0e5`

### Mandatory changes

None for the draft control layer.

The controls successfully distinguish:

- exact cases with zero budget;
- a genuinely rounded update with the exact rational result `(5/6, 13/12, 13/12)`;
- acceptance at the observed error and rejection below it;
- subnormal underflow/round-away behavior;
- invalid domains;
- NaN/infinity;
- and overflow/non-finite behavior from finite inputs even when `dt = 0`.

That is a good adversarial set for the logical checker.

### Non-blocking suggestions

If this PR is intended to satisfy #51's **native execution boundary** requirement, add an explicitly compiled/native regression that records or checks output bits from the kernel executable path. The current `#guard` controls are excellent Lean-level feasibility checks, but the native trust assumption should eventually be exercised in a way whose execution mode is unambiguous and documented.

Do not treat these empirical controls as an a priori error theorem; the PR currently avoids that mistake.

### Independent external reviewer conclusion

**SOURCE-LEVEL CONTROL PASS** at `8549497734c05c6b29b0257bc0f5450b5bbef404`.

The control set is strong enough for the proposed logical checker. Final E1 implementation acceptance should follow #51's freeze and should make the native-execution evidence boundary explicit.

---

# PR #56 — Propose conservative Euler MUSCL traces with paired admissibility fallback

**Reviewed head:** `5d76e8bea0390161aa388c92ec34f18d57bcbe50`  
**Base:** `8549497734c05c6b29b0257bc0f5450b5bbef404`

### Mandatory changes

None.

The proposal makes a clear and defensible method choice:

- conservative-variable componentwise minmod;
- raw traces `U_i ± s_i/2`;
- accept the pair only if **both** traces are admissible;
- otherwise replace both by the parent cell mean;
- use the owner's right trace and successor's left trace at each oriented face.

The paired fallback is important: it preserves the parent mean for MUSCL and avoids asymmetric one-sided fallback. The proposal is also careful not to claim positivity of the updated cell average or later RK stages.

The exact counterexample is correct. At `γ = 2`, the middle raw left trace has pressure `-1/8` even though all three parent cell means are admissible.

### Non-blocking suggestions

Keep the chosen variable set explicitly method-specific. Primitive or characteristic reconstruction should be separate methods, not hidden behind the same theorem names.

When this eventually gains a nonuniform variant, restate the geometry-dependent slopes rather than implying that this uniform proposal already covers them.

### Independent external reviewer conclusion

**RECOMMEND FREEZING THE UNIFORM EULER MUSCL TRACE PROPOSAL AS WRITTEN** at `5d76e8bea0390161aa388c92ec34f18d57bcbe50`.

The claims are precise and correctly stop at face admissibility.

---

# PR #57 — Prove Euler trace admissibility and exercise conservative MUSCL fallback

**Reviewed head:** `ff683462ce994fda3e55f48b99460ff415f76c96`  
**Base:** `5d76e8bea0390161aa388c92ec34f18d57bcbe50`

### Mandatory changes

None in the draft proof/control implementation.

The implementation proves the core proposal properties:

- selected traces are admissible whenever the parent mean is;
- admissible raw pairs are retained exactly;
- selected trace sum is `2 U`, hence their arithmetic mean is the parent state;
- the face takes the owner right trace and periodic successor left trace;
- constant states reconstruct to constant face states;
- the local admissibility predicate agrees with the existing 1D M1 conservative-state admissibility;
- the bad raw trace, fallback branch, valid nonconstant branch and periodic singleton seam are all exercised.

### Non-blocking suggestions

When promoted from `ReviewCases`, bind the face-admissibility, mean-preservation, raw-retention and constant-state properties separately rather than combining them into one monolithic certificate.

Keep the full-update positivity question explicitly outside this milestone.

### Independent external reviewer conclusion

**SOURCE-LEVEL PASS** at `ff683462ce994fda3e55f48b99460ff415f76c96`.

I would accept this implementation after #56 is formally frozen and the declarations are moved/bound under the normal production milestone workflow.

---

# PR #58 — Check a two-triangle oriented-face benchmark and hand off the review stack

**Reviewed head:** `d36848e44ff7dc951594b6c1e449f4c6696f2cff`  
**Base:** `ff683462ce994fda3e55f48b99460ff415f76c96`  
**CI:** Integration CI passed on this cumulative stack head.

### Mandatory changes

None.

The geometry and arithmetic independently check out:

- triangle areas are 1 and 2;
- the counterclockwise edge area-vector convention gives the listed vectors;
- each cell's area vectors close;
- the signed advection speeds are correct;
- the shared `CA` transfer is 6 from ABC to ACD;
- the boundary residual contribution is 21;
- cell residuals are 4 and 17;
- at `dt = 1/8`, the updated means are `3/2` and `63/16`;
- the weighted integral changes from 12 to `75/8`, exactly by the outward boundary transfer;
- reversing orientation and swapping states negates the flux;
- constant interior/exterior data gives zero residual.

This is a good first exact-real 2D geometry control because unequal cell areas make wrong-volume updates detectable.

### Non-blocking suggestions

When a production 2D API is introduced, keep the area vector as an oriented geometric quantity rather than normalizing it and then separately carrying face length; the current control's units and cancellation are especially transparent in area-vector form.

Do not let this benchmark imply a general mesh API or a multidimensional reconstruction theorem; the proposal correctly excludes those.

### Independent external reviewer conclusion

**RECOMMEND FREEZING THE TWO-TRIANGLE ORIENTED-FACE PROPOSAL AS WRITTEN**, and **PASS** the accompanying exact controls, at `d36848e44ff7dc951594b6c1e449f4c6696f2cff`.

---

# PR #59 — Plan the shared 1D face-trace interface with a second reconstruction family

**Reviewed head:** `80f5037eea1ba7a7e9dcb6a984cc7278f75e04d3`  
**Base:** `d36848e44ff7dc951594b6c1e449f4c6696f2cff`  
**CI:** Integration CI passed.

### Mandatory changes

None.

This is the correct timing for the reconstruction abstraction. The plan does not generalize “slope” or “limiter”; instead it identifies the common object as two **oriented face traces** consumed by one numerical flux.

The acceptance criteria are also appropriate: preserve the existing MUSCL behavior, add a structurally different reconstruction, check constants and a distinguishing nonconstant case, and reuse the existing conservative flux-form update.

### Non-blocking suggestions

Keep the eventual interface minimal. Do not add stencil radius, smoothness weights, polynomial degree or limiter fields to the shared reconstruction object unless a concrete consumer needs them; those are method-specific data.

### Independent external reviewer conclusion

**ACCEPT RECONSTRUCTION-INTERFACE PLAN** at `80f5037eea1ba7a7e9dcb6a984cc7278f75e04d3`.

This plan implements the architectural timing previously recommended for the repository.

---

# PR #60 — Implement scalar WENO-JS5 with a shared periodic reconstruction interface

**Reviewed head:** `99875ba63222d3f015cde2daff635fe4be6bb9e6`  
**Base:** `80f5037eea1ba7a7e9dcb6a984cc7278f75e04d3`  
**CI:** Integration CI passed.

### Mandatory changes

1. **Freeze the scientific WENO/reconstruction scope before accepting production implementation.** PR #59 is a roadmap/design trigger, but it does not freeze the exact Jiang–Shu candidate polynomials, smoothness indicators, ideal weights, epsilon hypothesis, orientation, uniform-grid restriction and promised theorem set. PR #60 puts those choices directly into production modules under `CFDLean`. That is inconsistent with the repository's proposal -> freeze -> implementation workflow.

   Add a scoped WENO/reconstruction contract (or equivalent reviewed scientific amendment), give the promised claims/result IDs, and then bind the production declarations to it.

I found no mandatory algebraic defect in the implementation itself. The uniform finite-volume WENO-JS5 formulas are correct:

- candidate face polynomials use the standard `(2,-7,11)/6`, `(-1,5,2)/6`, `(2,5,-1)/6` coefficients;
- smoothness indicators match the Jiang–Shu form;
- ideal weights are proportional to `1:6:3`;
- the right trace uses the reflected successor stencil;
- positive epsilon guarantees positive unnormalized weights;
- constant preservation and quadratic cell-average exactness are proved;
- the generic reconstruction step reuses the existing conservative update;
- the MUSCL adapter is definitionally equal to accepted FVN MUSCL;
- the six-cell seam control distinguishes WENO from MUSCL and the exact rational WENO traces recompute correctly.

### Non-blocking suggestions

Document the semantics for periodic grids with fewer than five distinct cells. The formula is still total because periodic indices repeat, but “WENO-JS5” no longer has a five-distinct-cell stencil or a fifth-order interpretation. Either document that as a repeated-stencil extension or later reject such solver configurations.

The shared `Reconstruction` object is appropriately small. Keep method-specific certificates separate rather than expanding the structure itself.

### Independent external reviewer conclusion

**REQUEST CHANGES — SCIENTIFIC CONTRACT/BINDING REQUIRED** at `99875ba63222d3f015cde2daff635fe4be6bb9e6`.

The mathematical implementation is otherwise sound and the new interface is the right abstraction. I expect acceptance after the exact WENO scope and promised results are independently frozen and bound.

---

# PR #61 — Plan non-uniform WENO and both executable model integrations

**Reviewed head:** `4a44b61833344832a433daa8852558390dee2df0`  
**Base:** `99875ba63222d3f015cde2daff635fe4be6bb9e6`  
**CI:** Integration CI passed.

### Mandatory changes

None in the roadmap change itself.

The dependency order is sensible:

1. geometry-aware scalar WENO;
2. Burgers executable integration;
3. Euler MUSCL/WENO integration;
4. complete executable regression matrix.

It correctly states that E1 and the first-order 2D control are independent of this reconstruction sequence.

### Non-blocking suggestions

Make the repository's scientific-freeze rule explicit in this four-step sequence: graded WENO and Euler WENO/system reconstruction are new numerical methods, not merely wiring tasks. Their mathematical choices should receive scoped proposal review before production acceptance.

For Euler, keep “face admissibility” separate from “updated-cell positivity”; the plan already does this and should continue to do so.

### Independent external reviewer conclusion

**ACCEPT SEQUENCING PLAN** at `4a44b61833344832a433daa8852558390dee2df0`.

The plan is architecturally coherent, subject to the normal proposal-freeze requirement for the new scientific methods it schedules.

---

# PR #62 — Extend scalar WENO-JS5 to graded periodic cell averages

**Reviewed current head:** `77a4ff4e7b53a522f07176486293da64acd60584`  
**Scientific/source commit reviewed:** `9f0d210c9bdefb91e6af61d2e8832f3c354899ab`  
**Current head adds:** hosted evidence only.  
**Current PR base:** `develop` at `3a3dbc26a42128822c5a274edaa0ee888b5c8411`  
**CI at review time:** Integration CI in progress on the evidence head. The previous source-head run passed all substantive Lean/driver/verifier steps and failed only the committed-evidence comparison; the current head records regenerated evidence.

### Mandatory changes

1. **Add/freeze a scientific contract for graded WENO.** This PR chooses the nonuniform candidate-polynomial geometry, geometry-dependent ideal weights and a particular nonuniform Jiang–Shu smoothness definition. Those are scientific method choices and should not enter the production library only through roadmap prose.

2. **Prove that the proposed “ideal weights” are actually ideal for the five-cell reconstruction.** The current theorems establish:
   - positivity of the weights;
   - quadratic exactness of each three-cell candidate;
   - constant preservation;
   - reduction to the uniform WENO formulas.

   What is missing is the key nonuniform linear-WENO property: with the geometry-dependent ideal weights, the linear combination of the three candidates reproduces the degree-4 five-cell reconstruction at the target face (equivalently, at least prove the cubic and quartic polynomial moments needed to determine those weights). Without that theorem, the implementation has not formally justified the central claim that these are the geometry-dependent **ideal WENO5 weights**.

   I independently checked the formula on representative unequal width tuples and it is consistent with the degree-4 reconstruction, so this appears to be a missing proof rather than a wrong formula.

3. **Fix the PR stacking/base before merge.** The head commit chain is built on PR #61, but the GitHub PR currently targets `develop`. As a result the PR contains the whole unaccepted #50–#61 stack. Retarget it to the #61 branch while those prerequisites are open, or wait until all prerequisites are accepted/merged and then rebase it cleanly onto `develop`.

4. Final acceptance requires the current Integration CI run to complete successfully.

### Non-blocking suggestions

The independent graded-seam rational controls are valuable and exercise both orientations.

The smoothness definition should be explained in the eventual contract as the derivative-square Jiang–Shu indicator integrated over the owning cell in owner-width coordinates. That makes clear what is being generalized from the uniform formula.

### Independent external reviewer conclusion

**REQUEST CHANGES** at current head `77a4ff4e7b53a522f07176486293da64acd60584`.

The source formulas look mathematically credible and the uniform reduction is strong evidence, but production acceptance needs the scientific freeze, a formal degree-4/ideal-weight theorem, a clean dependency base, and green final CI.

---

# PR #63 — Route WENO through Burgers SSPRK3 and the fv1d executable

**Reviewed current head:** `f5ea3e5761a2b4c79dbc020b7d9ac38295f952ea`  
**Main source commit reviewed:** `689dbfadcceb615c71cc7b505aaecddf22885318`  
**Current head additionally merges/records hosted evidence from #62.**  
**Current PR base:** `develop` at `3a3dbc26a42128822c5a274edaa0ee888b5c8411`  
**CI at review time:** Integration CI in progress. The earlier source-head run passed all substantive checks and failed only committed-evidence comparison.

### Mandatory changes

1. **Prove exact-real refinement for the actual SSPRK3 WENO kernel used by the driver.** `WenoRefinement.lean` currently proves `burgersWenoStep_refines` for one Forward Euler stage. The executable path, however, calls `burgersWenoSsprk3`, which recomputes WENO reconstruction at all three stages.

   Add a theorem showing the complete real `burgersWenoSsprk3` array operation represents the corresponding SSPRK3 composition of the mathematical graded-WENO step. Otherwise the production executable route is only formally connected for its internal FE stage, not for the operator it actually advances with.

2. **Resolve the upstream scientific blockers from #60/#62.** The executable should not be accepted as a production realization of a WENO method whose precise uniform/nonuniform contracts are not yet frozen.

3. **Fix the PR stacking/base.** The commit is downstream of #62 but the PR targets `develop`, so it currently carries the full unresolved predecessor stack. Retarget to #62, or wait/rebase after predecessors merge.

4. Final acceptance requires the current Integration CI run to pass.

### Non-blocking suggestions

Document or constrain the `--weno` behavior for `N < 5`. The periodic repeated-index formula is well-defined, but it should not silently inherit an ordinary fifth-order interpretation.

The driver correctly reconstructs again at every SSPRK3 stage rather than freezing face states from the initial state.

### Independent external reviewer conclusion

**REQUEST CHANGES** at `f5ea3e5761a2b4c79dbc020b7d9ac38295f952ea`.

The face orientation and executable WENO stage implementation look correct, but the formal refinement currently stops one level below the actual SSPRK3 solver operator. Add the full composition theorem and resolve the upstream contract/base issues before acceptance.

---

# PR #64 — Route MUSCL and WENO through the Euler density-wave driver

**Reviewed head:** `50dfc4a8d0809d7121f4449ad4e4e87a437923d9`  
**Parent source chain:** downstream of #63 source commit.  
**Current PR base:** `develop` at `3a3dbc26a42128822c5a274edaa0ee888b5c8411`  
**CI at review time:** Integration CI in progress.

### Mandatory changes

1. **Freeze the scientific scope for the Euler methods actually introduced here.** PR #56 covers **uniform conservative-component minmod MUSCL** traces. PR #64 goes materially beyond that:
   - nonuniform width-aware Euler MUSCL;
   - componentwise Euler WENO-JS5;
   - geometry-aware graded Euler WENO;
   - per-component nonlinear WENO weights;
   - cell-owned paired admissibility fallback for WENO.

   Those choices require their own reviewed contract/amendment before production acceptance. The roadmap sentence “specify the system weights and admissibility fallback” is not a scientific freeze.

2. **Add exact-real refinement for the production Euler reconstruction path.** `EulerReconstruction.lean` currently gives executable `eulerCell` and a Boolean validity lemma; the `ReviewCases` file demonstrates fallback examples. There is no production theorem connecting:
   - the real MUSCL `eulerCell` traces to the reviewed mathematical Euler trace construction;
   - the real WENO component traces to the mathematical graded-WENO reconstruction;
   - or the resulting `reconstructedStep` to a mathematical Euler FV step.

   The repository's execution architecture requires this seam to be explicit, especially because this PR is adding new production solver behavior rather than only a black-box demo.

3. **Fix the Euler timestep policy for reconstructed schemes, or explicitly redefine what it means.** The driver chooses
   `dt = 0.4 * minWidth / max(cell-mean endpoint speed)`
   using `model.speed q q` on cell means. But the Rusanov flux for MUSCL/WENO uses **reconstructed face states**, whose endpoint wave speeds can exceed those of the means.

   If the run is described as a CFL-0.4 reconstructed Euler run, compute the timestep from the reconstructed face states/speeds used by the flux (or from a proven safe upper bound). Otherwise explicitly state that 0.4 is only a cell-mean timestep heuristic and do not present it as the scheme's CFL condition.

   Runtime post-step admissibility rejection is useful, but it does not repair an underestimated pre-step wave-speed bound.

4. **Fix the PR stacking/base.** This PR is downstream of #63 but currently targets `develop`, carrying unresolved predecessor work. Retarget to #63 or rebase after predecessors are merged.

5. Final acceptance requires green Integration CI.

### Non-blocking suggestions

It is acceptable that this milestone does **not** prove positivity of updated cell means, provided the scope says so clearly. The runtime admissibility check should remain an execution safeguard, not be presented as a theorem.

For WENO, reconstructing conservative components with independent nonlinear weights is a legitimate method choice, but it must be named explicitly in the scientific contract because characteristic or shared-weight WENO would be different schemes.

### Independent external reviewer conclusion

**REQUEST CHANGES** at `50dfc4a8d0809d7121f4449ad4e4e87a437923d9`.

The executable mechanics and paired fallback are plausible, but this PR currently crosses too many new scientific and refinement boundaries at once. The missing exact-real correspondence and reconstructed-face timestep issue are blocking.

---

# PR #65 — Verify both models and all reconstruction modes on uniform and graded meshes

**Reviewed head:** `f04d651622335428a0ae44175acb6d2f390a59cd`  
**Parent:** `50dfc4a8d0809d7121f4449ad4e4e87a437923d9` (#64 source head)  
**Current PR base:** `develop` at `3a3dbc26a42128822c5a274edaa0ee888b5c8411`  
**CI at review time:** Integration CI in progress.

### Mandatory changes

1. **Do not accept this regression layer until #64's numerical-method/refinement/timestep blockers are resolved.** The tests can faithfully replay an implementation that is itself not yet scientifically accepted.

2. **Fix the PR stacking/base.** This PR is a single incremental commit on #64 but targets `develop`; retarget it to #64 while the stack is open, or rebase after all predecessors merge.

3. Final acceptance requires the current Integration CI run to pass.

I found no independent defect in the new reference/replay implementation itself. The Python reference is meaningfully independent of the production WENO formulas:

- it reconstructs candidate polynomials by solving cell-moment systems;
- determines ideal weights by reproducing cubic/quartic moments;
- applies the same owner/successor orientation independently;
- handles MUSCL geometry from widths;
- uses one shared Rusanov face flux;
- replays Burgers SSPRK3 explicitly;
- replays Euler Forward Euler in time;
- checks weighted conservation;
- compares implicit uniform, explicit equal-width and genuinely graded meshes;
- and exercises invalid option combinations/widths.

This is exactly the kind of black-box matrix that should accompany the production integration.

### Non-blocking suggestions

Decide explicitly whether `N = 1,2` with `--weno` is part of the supported method semantics. The current regression deliberately blesses the periodic repeated-stencil behavior. If the scientific WENO contract instead requires five distinct cells, change these cases into rejection tests.

Keep the Python reference as an independent implementation; avoid refactoring it to import coefficients directly from the production code.

### Independent external reviewer conclusion

**REGRESSION IMPLEMENTATION: SOURCE-LEVEL PASS, FINAL ACCEPTANCE BLOCKED BY UPSTREAM** at `f04d651622335428a0ae44175acb6d2f390a59cd`.

The new regression matrix is strong and independently constructed. It should be accepted after #64 is corrected/accepted, the PR stack is based cleanly, and final Integration CI is green.

---

# Recommended merge/review order

Given the present open stack, I recommend:

1. Merge/accept #50.
2. Freeze #51, then promote/review #52–#55 as one E1 implementation sequence.
3. Freeze #56, then accept/promote #57.
4. Freeze/accept #58.
5. Accept #59.
6. Before merging #60, add/freeze the exact uniform WENO/reconstruction contract and bind its results.
7. Accept #61 as sequencing documentation.
8. Retarget #62 -> #61, #63 -> #62, #64 -> #63, #65 -> #64 while the chain remains open.
9. For #62, add the graded-WENO scientific contract and degree-4 ideal-weight theorem.
10. For #63, add full SSPRK3 exact-real refinement.
11. For #64, freeze the Euler WENO/nonuniform reconstruction choices, add exact-real refinement, and fix/clarify reconstructed-face CFL selection.
12. Then accept #65's regression matrix once the corrected upstream stack is green.

This preserves the repository's strongest existing property: scientific choices are reviewed and frozen before their implementation becomes part of the trusted long-lived architecture.
