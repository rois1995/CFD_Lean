# Independent implementation review of fixed-mesh assembly

Please assess PR B against the [approved IDs and review decision](Assembly_Contract_Freeze.md), the
[proof map](../../references/MD-fixed-mesh-assembly.md), and the [result bindings](../../specifications/MD-fixed-mesh-assembly-results.json).
The numerical and theorem sources are at `66a2996caabcbdb44227c51b10077e3f8f31f7bd`, directly above
`0e1f9fbb9602a89daf6f9ce371f085ef3e8cb3a1`. The [implementation PR](https://github.com/rois1995/CFD_Lean/pull/75)
pins the final review head including this record and the regenerated evidence.

For MD-C, inspect the single transfer and opposite signs, including cellwise behavior under reversed orientation.
For MD-K, check that both the realized boundary transfer and interior transfer match the same linear map before using
closure. For MD-U, trace the volume cancellation and the invocation of MD-C. Compare the new real-valued triangle
instance with the original rational oracle. Check `cell_residuals` and `unequal_volume_update` separately. Assess
implementation acceptance independently of the contract freeze. Reindexing, new models, arrays and arithmetic error
estimates have later scopes.

## Local validation

Lean 4.36.0 (`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, `x86_64-unknown-linux-gnu`).
Replay the commands from the repository root with pinned dependencies. Lean ran with `LEAN_NUM_THREADS=2` in a
systemd scope capped at 16 GiB (8 GiB for the targeted check) and `MemorySwapMax=0`. Build caches affect the log text.
All commands below exited 0. SHA-256 values identify the captured stdout/stderr of each run.

| Command | Result | Log SHA-256 |
|---|---|---|
| `lake build --wfail CFDLean.Discrete.FixedMesh ReviewCases.OrientedTriangles ReviewCases.FixedMeshAssembly` | 4,523 build jobs | `ef40166021ae8d70aed624f4efbfea4fb8e46edd97c507af73857a2eeef2734e` |

The recorded type update adds exactly the four declarations in the MD result map. All 617 parent entries match in
both pretty and raw form. No trusted challenge statements changed.
| `lake build` | 18,677 build jobs | `2ff00c6331b5619c3a25bbe67e69e047ced8548a3b9b480f3faf368aa1e0028f` |

The recorded type update adds exactly the four declarations in the MD result map. All 617 parent entries match in
both pretty and raw form. No trusted challenge statements changed.
| `python3 scripts/verify.py` | 8,939 declarations in the inventory, 621 catalog entries and type pins | `4bfea66044019555e053b5aa1c25f536f8f2134c062f0d8e5d8d98f097156a80` |

The recorded type update adds exactly the four declarations in the MD result map. All 617 parent entries match in
both pretty and raw form. No trusted challenge statements changed.
| `sha256sum -c evidence/SHA256SUMS` | every listed file passed | `fc2891d8b606a06c525d965f2a25632a5e07c58f77867b53efd14b238cf711d0` |

The recorded type update adds exactly the four declarations in the MD result map. All 617 parent entries match in
both pretty and raw form. No trusted challenge statements changed.
| `python3 -m unittest discover -s scripts -p test_verify.py` | 79 verifier fixtures passed | `7966351906e8b83e5f82878539ff42fb03fc09976a6a3b9c4f6de7b9b27c253a` |

The recorded type update adds exactly the four declarations in the MD result map. All 617 parent entries match in
both pretty and raw form. No trusted challenge statements changed.
