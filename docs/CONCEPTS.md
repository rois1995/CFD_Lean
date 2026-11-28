# Concept-to-code map

Start with the [building-block tutorial](concepts/overview.md), then use the
[architecture graph](ARCHITECTURE-GRAPH.md) and [capability map](CAPABILITIES.md) to navigate the current repository.

For a specific theorem or result ID, start with the [theorem catalog](../catalog/README.md). For the claim's hypotheses
and proof chain, follow the milestone's [specification](../specifications/) and [reference note](../references/).

| Concept | Start here |
|---|---|
| Algebra and simplex calculus | [Foundations](../CFDLean/Foundations/Basic.lean), [simplex geometry](../CFDLean/Geometry/Simplex.lean) |
| Physical state and flux | [Burgers flux](../CFDLean/Physics/Burgers/Flux.lean), [Euler state](../CFDLean/Physics/Euler/State.lean), [Euler physical flux](../CFDLean/Physics/Euler/PhysicalFlux.lean) |
| Numerical flux | [Two-point interface](../CFDLean/Schemes/Scalar/NumericalFlux.lean), [Rusanov](../CFDLean/Schemes/Burgers/Rusanov.lean), [Roe](../CFDLean/Schemes/Roe/Flux.lean) |
| Mesh, geometry and boundaries | [Periodic neighbors](../CFDLean/Discrete/Periodic/Grid.lean), [median-dual geometry](../CFDLean/Geometry/MedianDual/README.md), [Euler boundary transfers](../CFDLean/Schemes/Boundary/Assembly.lean) |
| Spatial assembly and conservation | [Periodic flux differences](../CFDLean/Discrete/Periodic/FiniteVolume.lean), [periodic conservation](../CFDLean/Discrete/Periodic/Conservation.lean), [edge assembly](../CFDLean/Discrete/Assembly.lean) |
| Reconstruction and limiters | [MUSCL reconstruction](../CFDLean/Discrete/Periodic/Muscl.lean), [slope certificates and limiters](../CFDLean/Discrete/Periodic/Limiters.lean), [limited Rusanov scheme](../CFDLean/Schemes/Burgers/RusanovLimiters.lean) |
| Stability and entropy | [Total variation](../CFDLean/Discrete/Periodic/TotalVariation.lean), [Burgers CFL stability](../CFDLean/Schemes/Burgers/RusanovStability.lean), [scalar entropy certificates](../CFDLean/Entropy/Scalar/Certificates.lean), [Burgers entropy](../CFDLean/Entropy/Scalar/Burgers.lean) |
| Time integration | [Scalar Forward Euler](../CFDLean/Time/ForwardEuler.lean), [SSP composition](../CFDLean/Time/SSP.lean), [Euler lumped explicit update](../CFDLean/Time/ExplicitEuler.lean) |
| Native execution and refinement | [Array kernels, real refinement and driver](../CFDLean/Exec/README.md) |
| Paper 1 and shared numerical results | [JST1 statements and proofs](../specifications/JST1/README.md), [MC-N contract](../specifications/MC-N.md) |
| Trusted statement, bridge and comparator | [B0 statement](../CFDLean/Verification/BurgersB0Challenge.lean), [B0 bridge](../CFDLean/Verification/BurgersB0Verify.lean), [B0 comparator](../Challenges/BurgersB0.comparator.json), [B0 traceability](../references/Burgers-B0.md) |
