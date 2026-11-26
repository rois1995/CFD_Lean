# Architecture

[CFDLean.lean](CFDLean.lean) is the public library umbrella. Use the smallest relevant import when adding a module.
The folder describes the module's primary concern. Declaration namespaces can span folders. For example,
`CFDLean.Num` covers several numerical-core layers and `CFDLean.Burgers` covers both physics and schemes.
The [MR layout record](specifications/MR.md) and its [path map](specifications/MR-paths.json) locate moved files.
For inherited theorem types, see the [v4.36 port notes](evidence/port-types.md) and the [pinned type map](specifications/MC-port-types.json).

## Where should this code go?

| If the definition or proof is about… | Start here |
|---|---|
| Algebra, analysis or coordinates shared across methods | [Foundations](CFDLean/Foundations/) |
| A PDE state, physical flux or model-specific algebra | [Physics](CFDLean/Physics/) |
| Cell or face geometry, volumes, orientations or connectivity | [Geometry](CFDLean/Geometry/) |
| An operator reusable across numerical fluxes, such as periodic finite volume or reconstruction | [Discrete](CFDLean/Discrete/README.md) |
| A reusable entropy certificate, flux identity or entropy production | [Entropy](CFDLean/Entropy/) |
| A selected numerical flux, boundary algorithm or assembled scheme | [Schemes](CFDLean/Schemes/README.md) |
| A time update or a composition of time steps | [Time](CFDLean/Time/) |
| A computable kernel, arithmetic instance or refinement theorem | [Exec](CFDLean/Exec/README.md) |
| A statement or proof tied to a specific paper | [Papers](CFDLean/Papers/) |
| A trusted challenge statement or its proof bridge | [Verification](CFDLean/Verification/) and [Challenges](Challenges/) |

## Dependencies and proof boundaries

- Keep the PDE model, spatial discretization, time integration and execution distinct. Reuse the periodic grid and
  two-point flux interfaces in spatial operators. Assemble the concrete Burgers or Euler scheme where the selected
  flux and geometry meet. Keep generic SSP composition independent of that choice.
- Read the actual imports when placing code. The folder names do not form a total dependency order. For example,
  [periodic finite volume](CFDLean/Discrete/Periodic/FiniteVolume.lean) consumes the
  [two-point flux interface](CFDLean/Schemes/Scalar/NumericalFlux.lean), and
  [median-dual Roe aggregation](CFDLean/Geometry/MedianDual/RoeAggregation.lean) consumes the selected Roe flux.
- Keep execution dependencies out of the mathematical layers. The array kernels use a small arithmetic interface and
  run without Mathlib. The refinement modules import the kernel and the exact-real scheme so they can relate the two.
  [Main.lean](Main.lean) builds the native executable through the computable kernel.
- Keep trusted statements separate from their bridge proofs. Burgers theorem-only challenges use Mathlib. Execution
  challenges also use the hash-pinned kernel and arithmetic inputs named in [the verifier](scripts/verify.py).
  The default Lake build checks the bridges through the library globs. Comparator targets live in `Challenges/`.
- Keep geometry attached to its discretization. Burgers uses periodic cell averages, while Euler/Roe uses node-centered
  median-dual volumes and explicit boundary patches. Reuse a common lemma or interface where its hypotheses fit both.

See the [concept map](docs/CONCEPTS.md) for concrete files and the [design principles](roadmap/PRINCIPLES.md) for the
longer-term constraints.
