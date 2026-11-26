# Median-dual geometry

The [median-dual entry module](../MedianDual.lean) and files here provide node-centered geometry for the Euler/Roe line.

- [Local](Local.lean) and [Mesh](Mesh.lean) define simplex flags and the conforming tetrahedral mesh assumptions.
- [Edges](Edges.lean) and [Boundary](Boundary.lean) construct oriented edge areas and exterior patches. The entry
  module assembles dual volumes and proves volume partition and closure.
- [RoeAggregation](RoeAggregation.lean) relates geometric aggregation to the Roe flux. [Controls](Controls.lean) and
  [TwoCells](TwoCells.lean) provide exact examples.

See the [M3b proof map](../../../references/M3b.md) for definitions and incidence guarantees. The boundary transfers are
in [Schemes/Boundary](../../Schemes/Boundary/) and the explicit update is in [Time](../../Time/ExplicitEuler.lean).
