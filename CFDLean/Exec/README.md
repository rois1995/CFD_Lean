# Executable Burgers kernels

| Milestone | Computable kernel | Exact-real refinement |
|---|---|---|
| [E0](../../references/Burgers-E0.md) | [Kernel](Kernel.lean), first-order Rusanov | [Refinement](Refinement.lean) |
| [E0b](../../references/Burgers-E0b.md) | [MusclKernel](MusclKernel.lean), minmod MUSCL | [MusclRefinement](MusclRefinement.lean) |
| [E0c](../../references/Burgers-E0c.md) | [LimiterKernel](LimiterKernel.lean), selectable MUSCL limiter | [LimiterRefinement](LimiterRefinement.lean) |
| [FVNA](../../references/FV1D-nonuniform-array.md) | [NonuniformKernel](NonuniformKernel.lean), one width per cell: first order and MUSCL with a limiter | [NonuniformRefinement](NonuniformRefinement.lean), [NonuniformTransfer](NonuniformTransfer.lean) |

[RealScalar](RealScalar.lean) and [RealScalarSign](RealScalarSign.lean) instantiate the arithmetic interfaces over `ℝ`.
The refinement proofs connect arrays using those instances to the periodic schemes and transfer the stated guarantees.
The kernel is arithmetic-polymorphic through `Scalar α`. The native driver selects `Float` (binary64) and handles
initialization, parsing and diagnostics. Its arithmetic and output are outside the exact-real proof boundary.
[Driver](../../FVMain.lean) · [E1 backend contract](../../roadmap/NEXT.md#priority-2---e1-machine-arithmetic-strategy)

FVNA reuses the first-order FVA kernel [FV1D](FV1D.lean) for Burgers and Euler. Its exact real controls are in
[NonuniformControls](NonuniformControls.lean). [NonuniformKernelSmoke](NonuniformKernelSmoke.lean) runs the non-uniform
kernels in `Float` on the control data with `#eval`; it prints the outputs and proves nothing (`Float` error bounds
belong to E1).

From the repository root, run the first-order scheme or select a MUSCL limiter.

```bash
lake exe fv1d --model burgers 200 200 0.4
lake exe fv1d --model burgers 200 600 0.12 --limiter vanleer
```

The positional arguments select cell count, steps and CFL number. Limiter names are `none`, `minmod`, `mc`, `superbee`,
`vanleer` and `vanalbada`. `--muscl` alone is equivalent to `--limiter none`. This unlimited scheme can overshoot.
Use `--limiter minmod` to run the E0b scheme. Add `--dump` to print the final cell values after the diagnostics.

## Model-selecting driver

```bash
lake exe fv1d --model burgers 200 600 0.12 --limiter vanleer
lake exe fv1d --model burgers 48 12 .12 --weno --dump
lake exe fv1d --model burgers 4 3 .12 --widths .1,.2,.3,.4 --muscl --dump
lake exe fv1d --model euler 4 --dump
lake exe fv1d --model euler 4 --widths .1,.2,.3,.4 --dump
```

Burgers defaults to 200 cells, 200 SSPRK3 steps and CFL 0.4. Uniform runs sample the midpoint sinusoid
and report integral drift, extrema and periodic total variation.

Both models default to uniform spacing on the periodic unit interval. To supply a mesh, give
`--widths` followed by a comma-separated list in increasing cell order from the left boundary.
Supply one finite, strictly positive decimal per cell. The widths must sum to one within
an absolute tolerance of `1e-12`. With explicit widths Burgers samples the sinusoid at each
cell midpoint, uses the smallest width for its fixed timestep and reports width-weighted integrals.

Euler runs the [periodic density wave](../../benchmarks/fv1d/README.md) with four cells by default.
It initializes each cell with its analytic mean and advances with first-order Rusanov and Forward Euler.
Each step uses CFL 0.4, the smallest width and the current maximum endpoint speed. The last step ends at
`t = 1/8`. Output gives initial and final integrals and the width-weighted L1 errors against the translated
analytic cell means. Each dump row gives density, x-momentum density and total energy density in that order.
The driver checks density and pressure after each step. These are binary64 measurements.

Burgers accepts `--weno` on either mesh. Each SSPRK3 stage reconstructs both periodic traces from
the cell widths using scalar WENO-JS5 with regularization `1e-6`, then evaluates one Rusanov flux per face.
