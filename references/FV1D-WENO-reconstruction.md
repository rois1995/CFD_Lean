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
