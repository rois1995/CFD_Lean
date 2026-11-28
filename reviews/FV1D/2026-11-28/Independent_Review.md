# PR #66 — Independent external review

Reviewed head: `75b0f6cf790a3ed759126cbd50591c00d9281337`  
Base at review: `61a089eef19e02604ee047af682cd4334de8ec7c` (`develop`)  
State at review: draft, mergeable, branch behind `develop`  
Integration CI: in progress  
Paranoid comparator: skipped

### Mandatory changes

1. **Complete the E1 result map for frozen obligation 4.**

   The frozen E1 proposal has four obligations. `specifications/E1-results.json` currently binds only `E1-1`, `E1-2`, and `E1-3`.

   PR #66 does add the missing native-boundary work in substance:

   - `benchmarks/E1NativeReplay.lean` calls the production Float kernel;
   - it checks the exact three binary64 output words for the rounded control;
   - `references/E1.md` records the pinned Lean revision, executable hash, expected words, exact rational reference, and the distinction between logical Float semantics and native execution.

   That is the right evidence, but the frozen obligation is not represented in the result/evidence map.

   Add an explicit mapping for proposal obligation 4. It does not need to pretend to be a Lean theorem. For example, add a non-theorem evidence/control entry such as `E1-4` pointing to the native replay, toolchain identity, executable hash/provenance record, and the documented native-execution assumption. Alternatively add a clearly named top-level `native_execution_evidence` / `obligation_4` section if result IDs are reserved for theorem declarations.

   The important requirement is that an audit of the frozen four-obligation contract cannot conclude after reading only three mapped obligations.

2. **Strengthen the FVT-A production binding so it reaches the frozen M1 admissibility claim.**

   The frozen Euler trace proposal says the selected traces satisfy the existing **M1 density and pressure conditions**.

   `CFDLean.Exec.EulerTraces.face_admissible` currently concludes only the module-local predicate:

   `EulerTraces.admissible γ trace`.

   The bridge

   `CFDLean.Exec.EulerTraces.admissible_iff_m1`

   proves that this predicate agrees with `CFDLean.Conservative.Admissible`, but it is not part of the `FVT-A` result binding.

   The cleanest solution is to add and bind an explicit real-valued theorem such as `face_admissible_m1` that states the two selected traces satisfy the existing `Conservative 1` admissibility predicate. At minimum, include `admissible_iff_m1` as a supporting declaration attached to `FVT-A`.

   `FVT-M`, `FVT-R`, and `FVT-K` are correctly represented.

3. **Amend G-S before freezing the graded-WENO scope.**

   The proposed graded-WENO mathematics is sound in structure, and the newly added `G-I` obligation correctly addresses the proof gap identified in the previous review.

   In particular, the proposed linear weights reduce to `(1,6,3)` on equal widths, remain positive for positive widths, and independently reproduce cubic and quartic face moments in numerical checks. Requiring formal cubic/quartic moment lemmas is exactly the missing theorem needed to justify calling them geometry-dependent ideal WENO5 weights.

   However, `G-S` currently promises:

   > “Both traces at a graded seam match an independent cell-moment solve”

   without specifying the seam widths, cell averages, face, epsilon, or exact expected values in the contract itself. The proposed binding points to a future/current review control, but a frozen result should identify the exact control data or pin an immutable control revision.

   Before freezing G, put the exact asymmetric graded seam data and expected traces into the proposal, or explicitly identify and hash/pin the control file/revision that defines them.

4. **Amend the Euler execution scope before freezing E.**

   The proposed E scope correctly fixes the major scientific issues from the previous review:

   - conservative-component MUSCL is explicitly width-aware;
   - WENO is explicitly componentwise with separate nonlinear weights;
   - paired cell-owned fallback is explicit;
   - full-update positivity is excluded;
   - the reconstructed Euler timestep is now intended to use reconstructed face-state speeds rather than cell-mean speeds.

   Two parts still need to be made precise.

   **First, state the timestep formula explicitly.** Define, for every oriented face `i`, selected states `(L_i,R_i)` and

   `a_i = max(endpointSpeed(L_i), endpointSpeed(R_i))`.

   Then state the reconstructed-run timestep as the appropriate exact formula, e.g.

   `dt = min(T - t, 0.4 * min_i w_i / max_i a_i)`

   together with the behavior required if the global speed is zero/non-finite. This removes ambiguity from “maximum speed of the selected face states”.

   **Second, make E-R a concrete regression claim.** It currently says all three components agree with an independent reference on implicit-uniform, explicit-uniform, and graded meshes, but does not freeze the exact benchmark, cell count, graded widths, final time/step count, or comparison tolerance.

   Specify those values in the proposal or pin the exact regression-data/control revision. Otherwise E-R is not sufficiently falsifiable as a frozen promised result.

   I also recommend separating the current heterogeneous `E-A` item into independently auditable claims for:
   - selected-face admissibility;
   - first-order-driver parity;
   - reconstructed-face timestep selection.

   The split is not mathematically necessary, but it would make the result map substantially cleaner.

5. **Update the branch against the current `develop` before merge and re-run the final validation path.**

   PR #66 is currently `behind` its base. The exact review above applies to head

   `75b0f6cf790a3ed759126cbd50591c00d9281337`.

   A pure integration/rebase update that does not alter the reviewed contracts or production theorem statements does not require a new scientific review, but the final merge candidate should have coherent evidence on the actual final tree.

   Integration CI was still in progress when this review was completed. If the repository becomes private and CI is removed before merge, replace that gate with the repository's planned local validation record: exact parent/head SHAs, toolchain, commands, exit statuses, evidence hashes, and native replay identity.

### Non-blocking suggestions

- The archive claim is correct: `reviews/FV1D/2026-11-27/Independent_Review.md` records SHA-256 `9786d48a89972163144fa3b67fb49593a07ca57e3e6a187f9c1b1e69c71af28e`, which matches the Markdown review previously delivered by the independent reviewer.

- The three prior freeze records are faithful to the earlier verdicts:
  - E1 at `4b914b5bb3ea39ded55b958f5b29d72b7bd20c80`;
  - uniform Euler MUSCL traces at `5d76e8bea0390161aa388c92ec34f18d57bcbe50`;
  - two-triangle oriented-face control at `d36848e44ff7dc951594b6c1e449f4c6696f2cff`.

- The E1 production promotion is otherwise well executed. The production definitions/theorems preserve the semantics of the previously reviewed draft, the bit-pattern edge controls remain, the periodic seam/singleton controls remain, and the new compiled `e1NativeReplay` directly addresses the earlier request to exercise the native boundary explicitly.

- The FVT production promotion is also structurally sound. `pair_sum`, `retain_raw`, `face_constant`, the negative-pressure counterexample, valid nonconstant branch, and singleton periodic seam remain correctly exercised.

- **U — uniform WENO/reconstruction interface:** I find the proposed scope ready to freeze after the PR-level mandatory traceability items above are handled. The standard finite-volume WENO-JS5 candidate formulas, Jiang-Shu indicators, `1:6:3` ideal-weight ratio, reflected successor stencil, MUSCL parity, conservation reuse, quadratic exactness and constant preservation are appropriate. The explicit statement that repeated periodic indices for fewer than five distinct cells carry no distinct-stencil accuracy claim is a useful clarification.

- **G — graded WENO:** aside from the G-S precision issue, the proposal is much stronger than the earlier implementation-only state. The new `G-I` obligation is exactly the right correction. Keep the general fifth-order convergence claim excluded until it is actually proved.

- **B — Burgers WENO execution:** the scope is ready to freeze. `B-F` fixes the real Forward Euler refinement and `B-3` now explicitly requires the missing whole-SSPRK3 refinement with reconstruction recomputed at every stage. Keep machine-error certification outside this milestone as proposed.

- **E — reconstructed Euler:** the method choices themselves are coherent. Componentwise conservative WENO with component-specific nonlinear weights is a legitimate method, but preserving that choice explicitly in the contract is important because characteristic/shared-weight WENO would be a different method.

- For E1, consider storing the native executable hash as generated evidence rather than prose only, especially once CI is removed. A small deterministic provenance JSON would fit the private-repository workflow well.

- The two-triangle freeze correctly says it is only a benchmark/control and does not imply that the general multidimensional assembly contract has already been frozen. Preserve that distinction when the next 2D stack begins.

### Independent external reviewer conclusion

**REQUEST CHANGES — SMALL CONTRACT/BINDING CORRECTIONS, NOT A MATHEMATICAL REDESIGN** for PR #66 at:

`75b0f6cf790a3ed759126cbd50591c00d9281337`

The PR is a strong response to the previous review. It accurately archives the independent review, correctly freezes the three scopes that were previously recommended for freeze, promotes the reviewed E1 and uniform-Euler-trace drafts without changing their essential mathematics, and adds the missing native E1 replay evidence.

For the new WENO proposal, my scope decisions are:

- **U — uniform WENO-JS5 / reconstruction interface:** **RECOMMEND FREEZE**.
- **G — graded scalar WENO:** **APPROVE SUBJECT TO AMENDMENT**: keep `G-P` and `G-I`; make `G-S` identify exact pinned control data.
- **B — Burgers WENO execution:** **RECOMMEND FREEZE**.
- **E — reconstructed Euler execution:** **APPROVE SUBJECT TO AMENDMENT**: state the exact reconstructed-face timestep formula and make `E-R` a precisely specified/pinned regression claim.

For the promoted implementations:

- **E1:** source-level implementation remains **PASS**, and the new native replay satisfies the substance of the earlier native-boundary suggestion. Final implementation acceptance should follow explicit mapping of frozen obligation 4 and successful final validation.
- **FVT (uniform Euler MUSCL traces):** source-level implementation remains **PASS**. Final binding acceptance requires the M1 admissibility bridge to be explicit in `FVT-A`.

No new defect was found in the underlying E1 arithmetic logic, Euler paired fallback, uniform WENO formulas, graded-WENO weight formula, or Burgers WENO execution design.

After the five mandatory items above are resolved, I would expect PR #66 to be acceptable without another broad architectural review. A successor that changes only the requested scope wording/bindings, branch integration, and generated evidence can be reviewed as a focused delta.
