# Discrete operators

- [Mesh](Mesh.lean), [Galerkin](Galerkin.lean) and [Assembly](Assembly.lean) cover mesh operators, simplex and Galerkin
  identities, and edge-based assembly.
- [Periodic/Grid](Periodic/Grid.lean) gives the periodic neighbor permutation. [FiniteVolume](Periodic/FiniteVolume.lean)
  uses it to form flux differences, and [Conservation](Periodic/Conservation.lean) proves telescoping sums.
- [TotalVariation](Periodic/TotalVariation.lean) and [Convexity](Periodic/Convexity.lean) support stability proofs.
  [Muscl](Periodic/Muscl.lean) and [Limiters](Periodic/Limiters.lean) cover reconstruction and slope certificates.

For concrete fluxes and scheme-level guarantees, see [Schemes](../Schemes/README.md).
