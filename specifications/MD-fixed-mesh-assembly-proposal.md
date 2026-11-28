# Proposal for conservative assembly on a fixed mesh

**Decision requested.** Freeze MD-C, MD-K and MD-U below for implementation over the exact reals.
The parent is `15bc99d29bc7f97f15fa678f4d88d6093283d84f` on `develop`.
The first instance is the [independently frozen two-triangle control](../reviews/FV2D/Two_Triangle_Freeze.md).
Its acceptance covers that geometry and its prescribed boundary. Independent review of this proposal precedes PR B.

## Data and sign convention

| Input | Meaning |
|---|---|
| `Cell`, `InteriorFace`, `BoundaryFace` | Finite index types. Each physical interior interface occurs once. |
| `owner`, `neighbor` | Distinct adjacent cells for each interior face. Use `Assembly.Interfaces.tail` and `.head` respectively. |
| `boundaryOwner` | Single adjacent cell for each boundary face, given by `Assembly.Interfaces.owner`. |
| `A f`, `T b` | Oriented area vectors in `Fin d → ℝ`. `A f` points out of the owner into the neighbor. `T b` points out of its boundary owner. Their lengths carry face measure. |
| `V i` | Fixed measure of cell `i`. The update requires `0 < V i` for every cell. |
| `U i` | Cell mean in the state space `S`, supplied separately from mesh data. |

For an interior face the left trace belongs to the owner and the right trace to the neighbor. First order uses their means.
A reconstruction may supply traces directly. The model computes **one integrated outward flux** `F f` from those traces
and `A f`. The neighbor receives `−F f`. A boundary realization supplies one integrated outward flux `G b` to its owner.
The same assembly accepts prescribed transfers or transfers computed from exterior states. Boundary physics determines
which realizations are appropriate. The assembler consumes flux values and needs neither a normalizer nor boundary ghosts.

## Claims to freeze

**MD-C — interior cancellation and boundary balance.** For any additive commutative group `S`, define `R i` as the sum
of `F f` over owned interior faces, minus the sum over neighboring interior faces, plus `G b` over owned boundary faces.
Each face contributes `+F f`, `−F f`, and zero at all other cells. Thus `Σ i, R i = Σ b, G b`. An empty boundary gives zero
on the right. This holds for arbitrary flux arrays or functions, including vector-valued transfers. It requires neither
positive cell measures nor geometric closure. Reversing the stored orientation preserves cell residuals when the endpoints
are exchanged **and** the stored flux is negated. A two-state numerical flux recomputed under this reversal must satisfy
`H(right, left, −A) = −H(left, right, A)` for the two representations to agree.

**MD-K — cellwise constant-state residual.** Use a real module `S`. For a constant `C`, assume the integrated physical
flux is a linear map of the oriented area vector, `L_C : (Fin d → ℝ) →ₗ[ℝ] S`. Assume constant traces and equal-state
consistency, so `F f = L_C (A f)`. Separately require the actual boundary realization at `C` to give `G b = L_C (T b)`.
For each cell, assemble its geometric defect `D i` by applying the MD-C signs to `A` and `T`. Then `R i = L_C (D i)`.
The closure certificate `D i = 0` yields `R i = 0`. Closure alone describes the mesh. On a domain with boundary, a mismatch
between the supplied and compatible boundary flux adds its difference to the owning cell. Equal exterior states with a
consistent flux are one sufficient realization. Arbitrary prescribed inflow or wall data require their own compatibility check.

**MD-U — one Forward Euler balance.** For a real module `S`, positive fixed `V` and one common `dt : ℝ`, set
`U⁺ i = U i − (dt / V i) • R i`. Multiplying each cell change by its own measure and applying MD-C gives
`Σ i, V i • U⁺ i = (Σ i, V i • U i) − dt • (Σ b, G b)`. This gives conservation on an empty boundary and under zero net
boundary transfer. At `dt = 0` the field is unchanged. Under MD-K it is unchanged for every `dt`. These are algebraic
identities. Stability, admissibility and machine-error estimates require additional results.

## Proof map and independent control

- **MD-C.** Reuse the existing incidence convention and `Assembly.global_balance`. For general `S`, use finite signed
  sums and supply the agreement with the existing coordinate-vector residual. Scalar and system methods must invoke the
  same assembly result. Existing `residual_reverse` and `residual_reindex` provide coordinate-level comparison points.
  [Assembly](../CFDLean/Discrete/Assembly.lean)
- **MD-K.** Commute `L_C` with the signed sums. `Assembly.residual_map` and `constant_state_closed` exhibit the argument
  for coordinate states and the accepted Roe specialization. Instantiate the generic result by discharging flux and
  boundary hypotheses for each new model. [Assembly](../CFDLean/Discrete/Assembly.lean)
- **MD-U.** Cancel the positive volume cellwise, sum, then invoke MD-C. `euler_amount` and `mesh_common_balance` are the
  existing Euler-coordinate and median-dual precedents. [Explicit Euler](../CFDLean/Time/ExplicitEuler.lean)

Use the CCW cells `ABC`, `ACD` with `A=(0,0), B=(2,0), C=(2,1), D=(0,2)`, velocity `(1,2)`, means `(2,5)` and
prescribed exterior state `1`. The table records independent rational expectations for the generic instance. Keep the
original [benchmark](../benchmarks/ReviewCases/OrientedTriangles.lean) and its [contract](FV2D-oriented-face-proposal.md)
as the reference.

| Quantity | Expected value |
|---|---|
| Owner-oriented shared edge `CA`, area vector, flux | `ABC → ACD`, `(−1,2)`, `6` |
| Boundary flux per cell, outward residual per cell | `(−2,23)`, `(4,17)` |
| Cell measures, means after `dt = 1/8` | `(1,2)`, `(3/2,63/16)` |
| Total amount before and after, outward boundary rate | `12`, `75/8`, `21` |
| Any constant mean `k`, compatible exterior `k` | Both outward residuals are zero |

Check individual cells as well as totals. A shared `+6` at both cells gives residuals `(4,29)`. Exchanging owner and
neighbor while retaining the stored `+6` gives `(−8,29)` and **still sums to 21**. Duplicating the interior record gives
`(10,11)`, also summing to 21. Using the first cell's measure for the second update gives `23/8` in cell two. The accepted
values distinguish all four faults.

## Scope after freeze

PR B implements these three claims and their two-triangle instance. Fixed-velocity upwind advection on a second patch
with several interior faces precedes extraction of a common geometry record and the generic reindexing result. Until then,
pass the existing topology and the geometry functions explicitly. Array traversal and its real-number refinement follow
those two examples. First-order 2D Euler then supplies a new flux adapter. Its scientific contract gets a separate freeze.
The executable driver follows both model refinements. Multidimensional reconstruction begins with its own proposal after
first-order validation. Arithmetic certification follows the operations of each concrete backend independently. Moving
meshes, refinement, viscous terms and parallel traversal remain outside this stack.
