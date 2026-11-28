# Reconstruction and execution proof map

The [scientific proposal](../specifications/FV1D-WENO-reconstruction-proposal.md) records the
formulas, indexing and hypotheses. The [result map](../specifications/FV1D-WENO-reconstruction-results.json)
binds each claim to its declaration or executable control. Catalog status tracks implementation review.
Periodic stencils repeat indices on meshes with fewer than five cells. The exact-real results and
binary64 regressions describe different arithmetic backends.

| Claim | Declaration or control | Coverage |
|---|---|---|
| U-C | [`step_weighted_sum`](../CFDLean/Discrete/Periodic/Reconstruction.lean) | The width-weighted update sum is conserved for any oriented reconstruction. |
| U-C | [`step_constant`](../CFDLean/Discrete/Periodic/Reconstruction.lean) | Constant-preserving traces give a constant-preserving update. |
| U-M | [`muscl_step`](../CFDLean/Discrete/Periodic/MusclReconstruction.lean) | The MUSCL reconstruction adapter gives the existing graded MUSCL step. |
| U-W | [`weight_pos`](../CFDLean/Discrete/Periodic/Weno.lean) | Positive regularization and ideal weight give a positive nonlinear weight. |
| U-W | [`edge_quadratic`](../CFDLean/Discrete/Periodic/Weno.lean) | Uniform WENO reproduces a quadratic from its cell averages. |
| U-W | [`wenoJS5_constants`](../CFDLean/Discrete/Periodic/Weno.lean) | Both oriented uniform WENO traces preserve constants. |
| U-W | [Reconstruction.lean](../benchmarks/ReviewCases/Reconstruction.lean) | Six-cell uniform seam comparison. |
| G-P | [`ideal_positive`](../CFDLean/Discrete/Periodic/GradedWeno.lean) | The three ideal weights are positive on positive cell widths. |
| G-P | [`gradedWeno_constants`](../CFDLean/Discrete/Periodic/GradedWeno.lean) | Graded WENO preserves constant face traces in both orientations. |
| G-P | [`edge_quadratic_graded`](../CFDLean/Discrete/Periodic/GradedWeno.lean) | Graded WENO exactly reconstructs a quadratic from its interval averages. |
| G-P | [`edge_uniform`](../CFDLean/Discrete/Periodic/GradedWeno.lean) | Equal widths recover the uniform WENO reconstruction. |
| G-I | [`ideal_cubic_quartic`](../CFDLean/Discrete/Periodic/WenoMoments.lean) | The linear ideal weights reproduce cubic and quartic moments on positive widths. |
| G-S | [GradedWeno.lean](../benchmarks/ReviewCases/GradedWeno.lean) | Exact rational graded seam in both directions. |
| B-F | [`burgersWenoStep_refines`](../CFDLean/Exec/WenoRefinement.lean) | A Burgers WENO forward stage agrees with the exact-real graded finite-volume step. |
| B-3 | [`burgersWenoSsprk3_refines`](../CFDLean/Exec/WenoRefinement.lean) | The three native stages over the reals agree with SSPRK3 on the same periodic mesh. |
| E-T | [`eulerCell_refines`](../CFDLean/Exec/EulerReconstructionRefinement.lean) | Native reconstructed pairs over the reals agree with the mathematical Euler cell traces. |
| E-F | [`eulerReconstructedStep_refines`](../CFDLean/Exec/EulerReconstructionRefinement.lean) | The reconstructed native step over the reals agrees with the oriented M1 Euler flux update. |
| E-A | [`selectEulerPair_valid`](../CFDLean/Exec/EulerReconstruction.lean) | Both selected endpoints pass the validity test when their mean passes. |
| E-A | [`positiveState_iff_m1`](../CFDLean/Exec/EulerReconstructionRefinement.lean) | The exact-real endpoint test agrees with M1 conservative-state admissibility. |
| E-A | [EulerReconstructedStep.lean](../benchmarks/ReviewCases/EulerReconstructedStep.lean) | Raw and fallback branches at reconstructed Euler faces. |
