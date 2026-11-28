# Proposed contracts for 1D WENO and reconstructed Euler

Independent scope decisions are requested separately for U, G, B and E. Each row identifies a promised result
and the declaration or control proposed to discharge it. Production binding and pinning follow approval.
The model is exact-real, cell-centered, periodic finite volume. Each numerical face uses its owner's right trace
and its successor's left trace. Both adjacent cells consume the same flux. Strictly positive cell widths and
strictly positive WENO regularization ε are required. Periodic indexing repeats cells when fewer than five
distinct cells exist. Such runs have a defined stencil and carry no distinct-stencil accuracy claim.

## U — uniform WENO-JS5 and the reconstruction interface

For means (a,b,c,d,e) about the owner, the three right-face candidates are (2a−7b+11c)/6,
(−b+5c+2d)/6 and (2c+5d−e)/6. Each indicator is 13k²/12+g²/4. The three (k,g) pairs are
(a−2b+c,a−4b+3c), (b−2c+d,b−d), and (c−2d+e,3c−4d+e). Normalize weights proportional to
(1,6,3) divided componentwise by (ε+β)². Reverse the successor stencil for the right trace.
[Jiang and Shu (1996)](https://doi.org/10.1006/jcph.1996.0130)

| ID | Promised claim | Proposed declaration in CFDLean.FV1D.Reconstruction |
|---|---|---|
| U-C | Width-weighted conservation for arbitrary face traces and constant-state preservation under constant traces | step_weighted_sum, step_constant |
| U-M | The MUSCL adapter reproduces the existing FVN step for any limiter and two-point flux | muscl_step |
| U-W | Strict positivity of unnormalized weights, quadratic cell-average exactness, constant traces | Weno.weight_pos, Weno.edge_quadratic, wenoJS5_constants |

## G — graded scalar WENO

Measure lengths in units of the owning cell's width. Each candidate is the quadratic whose three interval
averages equal the stencil data. Evaluate at the owning endpoint. Integrate the squares of its first and
second derivatives over the unit owner cell for the indicator. For q(x)=Ax²+Bx+C about its center this is
B²+13A²/3. Reflect the widths and states together for the opposite face.

For widths (a,b,1,d,e), let L=a+b+1, R=d+e, p=10R/(L+R), q=10L/(L+R). The linear weights are
p d/(L+d), p L/(L+d)+q R/(b+1+R), q(b+1)/(b+1+R). Divide each by its own (ε+β)² and normalize.
The degree-four reproduction obligation applies to the **linear** weights. Nonlinear WENO must reproduce
quadratics and constants. A general fifth-order convergence result is a separate claim.

| ID | Promised claim | Proposed binding |
|---|---|---|
| G-P | Positivity, constant preservation, local quadratic exactness and equal-width specialization | ideal_positive, gradedWeno_constants, edge_quadratic_graded, edge_uniform |
| G-I | Linear weights reproduce the cubic and quartic moments at the target face for all positive widths | New cubic and quartic moment lemmas required |
| G-S | Both traces at a graded seam match an independent cell-moment solve | ReviewCases.GradedWeno rational controls |

## B — Burgers execution

Use the existing Rusanov model and SSPRK3 coefficients. For each stage recompute the WENO face pairs from
that stage's means. Preserve the accepted first-order/MUSCL driver transcript. The production binary64 route
uses ε=1e−6 and the original midpoint initialization. Its machine-error budget is outside B.

| ID | Promised claim | Proposed binding |
|---|---|---|
| B-F | The real array Forward Euler stage equals the graded finite-volume step | burgersWenoStep_refines |
| B-3 | The complete real array SSPRK3 operator equals the three-stage composition on the same mesh | New whole-operator refinement required |

## E — reconstructed Euler execution

Use the ideal-gas conservative state (ρ,m,E) with γ>1 and admissible means (ρ>0, p>0). MUSCL uses componentwise
minmod on the two neighboring differences scaled by 2wᵢ/(w_neighbor+wᵢ). The uniform case is governed by
the frozen [Euler MUSCL scope](FV1D-euler-traces-proposal.md). WENO uses G separately on each conservative
component, with its own indicators and weights. If either of the two raw endpoints of a cell is inadmissible,
replace both by that cell's mean. WENO endpoint averages need not equal their parent mean.
The flux is Rusanov with the maximum ideal-gas endpoint speed. For reconstructed runs choose the step from
the maximum speed of the selected face states, the minimum width, the factor 0.4 and the remaining time.
Preserve the first-order timestep policy. The native driver also checks finiteness and rejects inadmissible updates.

| ID | Promised claim | Proposed binding |
|---|---|---|
| E-T | Real executable MUSCL and WENO traces equal their respective mathematical cell-owned traces, including fallback | New trace correspondences required |
| E-F | Real reconstructed Forward Euler update agrees with the conservative periodic Euler face-flux update | New assembled-step refinement required |
| E-A | Admissible means imply admissible selected endpoints; unchanged accepted first-order behavior and correct reconstructed-face timestep | selectEulerPair_valid plus real admissibility correspondence and executable controls |
| E-R | All three conserved components agree with an independent reference on implicit uniform, explicit uniform and graded meshes | FV1D executable regression matrix |

Full-update positivity, binary64 certification, general convergence order, primitive-variable and characteristic
WENO are outside this proposal. Independent reviewers should freeze, amend or reject each scope and identify
mandatory findings separately from suggestions before production acceptance.
