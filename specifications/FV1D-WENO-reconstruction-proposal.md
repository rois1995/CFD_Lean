# Proposed contracts for 1D WENO and reconstructed Euler

The [independent review](../reviews/FV1D/2026-11-28/Independent_Review.md) recommends freezing U and B
and approves G and E subject to the amendments below. Each row identifies a result and its declaration or control.
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

**G-S fixture.** Number the six periodic cells 0 through 5. Set their widths to (1,2,3,4,5,6),
their means to (1,2,4,3,1,0), and ε to 1. On the oriented face from cell 5 to cell 0, the owner-right
trace is 18404544825410991576178677 / 30404425815732402608015224 and the successor-left trace is
289716345724523430316611 / 401443434426759937064444. Both are exact rational equalities.
[Immutable seam control](https://github.com/rois1995/CFD_Lean/blob/77a4ff4e7b53a522f07176486293da64acd60584/benchmarks/ReviewCases/GradedWeno.lean)

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
At oriented face i let Lᵢ be the selected right trace of cell i and Rᵢ the selected left trace
of its successor. With s(q) = |m/ρ| + √(γ p/ρ), the Rusanov face speed is aᵢ = max(s(Lᵢ),s(Rᵢ)).
For 0 ≤ t < T and a = maxᵢ aᵢ > 0 the reconstructed Forward Euler step uses
`dt = min(T − t, 0.4 · minᵢ wᵢ / a)`. For a = 0 use T − t. The driver rejects a negative or
non-finite computed face speed and stops before an update if dt is non-finite or t + dt ≤ t.
It rejects non-finite or inadmissible updated means. The first-order driver retains its cell-mean speed policy.

| ID | Promised claim | Proposed binding |
|---|---|---|
| E-T | Real executable MUSCL and WENO traces equal their respective mathematical cell-owned traces, including fallback | New trace correspondences required |
| E-F | Real reconstructed Forward Euler update agrees with the conservative periodic Euler face-flux update | New assembled-step refinement required |
| E-A | Admissible means imply admissible selected endpoints | selectEulerPair_valid and the M1 admissibility correspondence |
| E-P | Preserve the accepted first-order density-wave driver behavior | First-order density-wave and explicit-width parity controls |
| E-D | Select dt from the chosen face states with the rule above | Driver timestep controls and the E-R independent adaptive replay |
| E-R | All three conserved components agree with an independent reference on implicit uniform, explicit uniform and graded meshes | FV1D executable regression matrix |

**E-R fixture.** On the unit periodic interval take N = 8, γ = 2, pressure 1, velocity 2 and
ρ(x,0) = 1 + (π/8) sin(2πx). Initialize exact cell averages, m = 2ρ and E = 1 + 2ρ.
Advance to T = 1/8 with Forward Euler, CFL 0.4 and WENO ε = 10⁻⁶. Use implicit uniform widths,
explicit widths (1,…,1)/8 and graded widths (1,3,2,4,1,1,2,2)/16 in that order. First order,
minmod and WENO each take 10 steps on both uniform inputs. On the graded input they take 19, 19
and 20 steps respectively. Compare every dumped density, momentum and energy to the independent
adaptive reference with absolute tolerance 2·10⁻¹⁰. Each component's width-weighted drift must be
at most 2·10⁻¹¹; implicit and explicit uniform dumps must agree to 2·10⁻¹¹.
[Immutable regression](https://github.com/rois1995/CFD_Lean/blob/17673f957f52093cadd3983c1b472456ac7b6ad2/scripts/test_fv1d.py) ·
[Independent moment solve and flux replay](https://github.com/rois1995/CFD_Lean/blob/17673f957f52093cadd3983c1b472456ac7b6ad2/scripts/fv1d_reference.py)

Full-update positivity, binary64 certification, general convergence order, primitive-variable and characteristic
WENO are outside this scope.
