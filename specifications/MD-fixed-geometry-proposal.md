# Proposal for fixed-mesh geometry and relabeling

**Decision requested.** Freeze FG-R, the invariance of a cell residual and its Forward Euler update under a relabeling
of cells, interior faces and boundary faces. The proposal is based on `5470efca41adb07fa3e6d70e5b6b69d0ee5501c3`. The scalar controls on the
[unequal triangles and four-cell patch](../benchmarks/ReviewCases/ScalarAdvection.lean) now exhibit the data shared
by concrete physics adapters. The scalar implementation has its own independent acceptance checkpoint.

## Minimum common input

Both controls use `Assembly.Interfaces C I B`, a cell measure `V : C → ℝ`, interior area vectors `A : I → Vector d`,
and outward boundary area vectors `T : B → Vector d`. Bundle exactly these four inputs in a `FixedMesh.Geometry`
record. Retain the existing interface record for incidence. Keeping another copy of owner and neighbor functions would
introduce a second source of orientation. Keep positive measures and cell closure as separate hypotheses where needed.
The field `U`, realized face transfers `F` and `G`, prescribed exterior data, model and timestep remain arguments to
their respective operations. A triangle's coordinates and a patch's construction rules belong to the example that
produces the geometry. Both examples must instantiate and exercise the same record through the accepted assembler.

## FG-R

Let `c : C ≃ C'`, `e : I ≃ I'` and `b : B ≃ B'` be independent equivalences. Reuse `Interfaces.reindex c e b`.
At new index `j`, look up volumes and states using `c.symm j`, interior vectors and transfers using `e.symm j`, and
boundary vectors, data and transfers using `b.symm j`. Transport the endpoints forward by `c`. This preserves the
original owner-to-neighbor face orientation. The sign of an integrated transfer changes only if the orientation itself
is changed, as handled by `FixedMesh.residual_reverse`.

- **Residual.** For every additive commutative group of transfers and old cell `i`, the new residual evaluated at
  `c i` equals the old residual at `i`. Use equivalences of the finite face sums. Compare to the accepted
  coordinate-vector specialization `Assembly.residual_reindex`. [Assembly](../CFDLean/Discrete/Assembly.lean)
- **Step.** For real-module states, transported `U` and `V`, and one common `dt`, the updated value at `c i` equals
  the old updated value at `i`. Apply residual invariance to `FixedMesh.step` with the corresponding cell's measure.
  Take positive volumes for the physical update. The transported certificate follows by substitution. Applying the
  same residual theorem to area vectors transports cell closure. [Fixed-mesh assembly](../CFDLean/Discrete/FixedMesh.lean)

## Exact controls

For the two triangles, exchange the cell labels. In the new order the volumes must be `(2,1)`, the residuals `(17,4)`
and the updated means `(63/16,3/2)`. Check the oblique transfer retains its original orientation and value `6`.

For the four-cell patch, use the original zero-based numbering. Map each old cell `i` to `(i+1) mod 4`, each old
interior face `f` to `(f+3) mod 4`, and each old boundary index `(i,side)` to `(3−i,!side)`. Boundary labels and
interior face labels therefore move independently of cell labels. In increasing new index order, the interior transfers
are `(4,−2,−4,2)`, the residuals `(8,1,3,6)` and the updated means `(3,7/8,21/8,5/4)`. Total boundary exchange is
still `18`. Check individual values so that a wrong inverse permutation cannot pass by preserving the global sum.
Use transported geometry and fields with the same production scalar adapter on both meshes.

The proposed result covers relabeling of fixed topology. Executable index validation and the correspondence of a
face-loop array kernel with the mathematical step belong to PR E. Mesh import, moving cells, reconstruction and
new fluxes retain separate milestones. Independent freeze of FG-R precedes its implementation.
