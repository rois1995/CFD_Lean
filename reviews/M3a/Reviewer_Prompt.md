# Reviewer prompt: M3a abstract assembly

Please independently review **M3a (M3-I/R/O and conditional M3-C)** in the private repository `rois1995/CFD_Lean`.

**Mathematical candidate:** `a70270c3f771e66bcaaebc18b8480c32f9606b1e`.

Start with [the checkpoint and evidence](https://github.com/rois1995/CFD_Lean/blob/main/reviews/M3a/README.md). Accepted full M2 is pinned at `ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`; M3 scientific approval/freeze is `3189a603b3f6af953f0828d6b2e239320fd2cd20`, following the reviewed proposal and Andrea's explicit authorization.

Check the exact incidence/scatter definition and boundary ownership; derive global boundary balance for arbitrary transfers without assuming closure or cancellation. Verify that the concrete Roe transfer uses the actual accepted numericalFlux with exactly one integrated area factor. Separately check the accepted M2 reversal connection to independently evaluated outward endpoint fluxes, arbitrary selected edge reversals, zero area and simultaneous transported node/edge/boundary relabeling.

Review the common-state result: compatible boundary transfers and the actual M1 physical-flux linear map must give the residual as physicalFlux on the metric defect. Zero metric defect is conditional input in M3a; this is not the promised concrete M3-G theorem. Inspect the nonempty admissible actual-Roe controls with compatible and incompatible boundary data, including the nonzero relabeled residual.

Verify preservation of every accepted mathematical source and all 66 M2 bindings/stages/types. Inspect the extended guard, frozen M3 metadata/part layout, literal full Git diff and expected-type controls. Check that M3b's G/V and concrete C remain explicitly deferred rather than accepted through the conditional result. The worker reports 84 cumulative bindings, 73 Lean examples and 11 checker fixtures, with a full inventory of 672 records and no unsafe or forbidden dependency reachable from 458 safe roots. Independently inspect the new structure/transport compiler-auxiliary classifications.

Independently run scripts/reproduce.sh on the exact candidate from a clean checkout without .lake, with both cache controls, nine fresh pinned sources and local pinned widget compilation. Compare all five deterministic outputs byte for byte. The fresh worker source replay passed, including all 40 pre/post source checksums and five byte-identical deterministic comparisons. Treat submitted logs as evidence to verify, not independent acceptance.

Return a **scoped M3a verdict** with blockers/conditions and qualified declaration/file references, and state the next permitted work under the approved M3a/M3b plan. **Full M3 acceptance is outside this checkpoint:** M3b must still derive tetrahedral median-dual geometry/volume identities and instantiate this same residual/constant-state interface. Boundary algorithms, time stepping, entropy/positivity repairs and SU2 correspondence remain outside M3a.
