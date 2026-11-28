# Independent implementation review of fixed-mesh scalar advection

Please review SA-F, SA-K and SA-C against the [frozen contract](../../specifications/MD-scalar-advection-proposal.md)
and [declaration map](../../references/MD-scalar-advection.md). The scientific source at
`ec7355a39d0e608e04c0ac3c6508c72f491b9ec9` has exact parent `e53022162a38ec3c482c307f96c66339b354d161`.
[PR #77](https://github.com/rois1995/CFD_Lean/pull/77) pins the final review candidate with the generated evidence.

- SA-F has separate equal-state, reversal and zero-speed theorems. In the concrete zero-speed check, velocity `(2,−1)`
  and area `(1,2)` give a zero transfer for unequal means `3` and `7`.
- For SA-K, inspect the shared physical linear map and the two distinct applications of consistency. Cell closure
  discharges MD-K. The update uses `FixedMesh.step_zero_residual` for arbitrary `dt`.
- For SA-C, check how the prescribed exterior state enters `boundaryFlux`. The scalar global and weighted balances
  invoke the MD theorems with those realized transfers.
- Both controls call the production face functions and assembler. On the unequal triangles, check both orientations,
  `(4,17)`, `(3/2,63/16)` and `12 → 75/8`. On the patch, check every shared transfer, all eight exterior edges,
  cell residuals `(1,3,6,8)` and amount `10 → 31/4`. Both examples prove closure and constant preservation cellwise.

## Reproduction

Lean 4.36.0 (`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, Linux x86_64). Use the pinned Lake dependencies.
Local Lean commands use `LEAN_NUM_THREADS=2` under a 16 GiB systemd memory cap with swap disabled. Run the targeted
build, `lake build`, `python3 scripts/verify.py`, and `sha256sum -c evidence/SHA256SUMS` from the candidate root.
The PR carries the full local build and verification results. The following local checks exited 0. Digests identify
combined stdout and stderr, including any run-specific timing.

| Command | Output SHA-256 |
|---|---|
| `lake build --wfail CFDLean.Schemes.ScalarAdvection ReviewCases.ScalarAdvection ReviewCases.FixedMeshAssembly ReviewCases.OrientedTriangles` | `175c29b033e7ce358885828534e232bb2ac3713a92bbab42fea5e6b490dd52a8` |
| `python3 -m unittest discover -s scripts -p test_verify.py` | `4849352cd4b8c56d9da109bfe36d5c466143ae53a2c56bb44e8874b134f70393` |
| `sha256sum -c evidence/SHA256SUMS` | `ee552d456d8ae0ffc1eb543ba29ff439c6fa532a05888fc76de7e2dc01361c7f` |
| `PYTHONPATH=scripts python3 -m unittest test_capabilities test_graph_docs test_import_graph test_docs_site` | `ff9a18361965317227f68e1e2f6484c175bddf5ab3c2088c47d7de9214be4c46` |
| `python3 -m mkdocs build --strict --site-dir /tmp/mdsa-review-site` | `e9b78b46bdcf5fb3eb9eea58899175eec7cebd80601b7292e6bc8e682640eaa8` |

The [CI evidence artifact run](https://github.com/rois1995/CFD_Lean/actions/runs/46149197657) recorded 629 promised theorem types. All 621 parent entries match exactly, and the eight added entries are precisely the SA result bindings. Geometry extraction, executable refinement, Euler, higher-order methods and arithmetic-error bounds retain their own milestones.
