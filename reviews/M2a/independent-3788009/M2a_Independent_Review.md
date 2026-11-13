# Independent review of CFD_Lean M2a and the proof audit

**Verdict — Accept M2a (M2-J). No blocking finding or outstanding acceptance condition for this candidate.** The independent cold build passed, all eight expected theorem types elaborated, and the audit accepted exactly the permitted foundations.

**Scope.** M2-J in the exact-real, three-dimensional, stationary ideal-gas Euler specification. This checkpoint delivers the physical flux Jacobian required for a later proof that the two-state Roe matrix tends to the physical derivative. Roe averaging, the flux-jump identity, eigenstructure and the numerical flux remain later obligations.

| Record | Immutable revision |
|---|---|
| Accepted M1 mathematics | `0a88e36b3810cd5adc3881db526ca8a35f81afbb` |
| Approved M2 contract | `79fd2a03d7b15325c56a88ec83991b4fb4f498bb` |
| M2a mathematical candidate reviewed | `3788009de306d80e002976e66ba2b1103e2dbd83` |
| Worker checkpoint and archived replay | `4d845ad07166b926818b4ce7c8015c80ed97fd94` |

## Eight statement bindings

The two namespace prefixes in the table are `C = CFDLean.Coordinates` and `J = CFDLean.PhysicalJacobian`. File lines refer to the candidate. The derivative is with respect to the five conservative state coordinates. The gas parameter and face vector are fixed throughout.

| Theorem | Hypotheses, conclusion and assessment |
|---|---|
| `C.decode_encode` · Coordinates.lean:19 | Every conservative record in three dimensions survives the round trip. The proof reconstructs all three momentum components in order. |
| `C.encode_decode` · Coordinates.lean:28 | Every five-vector survives the reverse round trip. Density is coordinate 0, energy density is coordinate 4. Together the chart results cover the entire coordinate space. |
| `J.hasFDerivAt_coordinateFlux` · PhysicalJacobian.lean:90 | For every real γ and every fixed n, density ≠ 0 suffices. At line 43 the differentiated function unfolds to `encode (physicalFlux γ (decode x) n)`. The five component functions used in the product-rule proof are identified with this function by definitional equality. The proof differentiates pressure and the normal velocity quotient. |
| `J.isOpen_admissible` · PhysicalJacobian.lean:144 | For each fixed γ, the coordinate preimage of the M1 admissibility predicate is open. At an admissible point, density is positive, so local pressure continuity follows from its derivative. This does not require a continuity claim across vacuum. |
| `C.unitNormal_dot_self` · Coordinates.lean:58 | For S ≠ 0, normalized S has Euclidean dot product one with itself. Lines 41–55 give the square-root length and its strict positivity. `area_oblique` at line 77 yields √13 for (2,3,0). |
| `J.hasFDerivAt_integratedFlux` · PhysicalJacobian.lean:135 | For nonzero density and S ≠ 0, the derivative of the M1 flux evaluated at S equals the Euclidean area times the Jacobian at its unit normal. The proof reconstructs S and applies homogeneity in its directional argument exactly once. |
| `J.jacobian_action` · PhysicalJacobian.lean:154 | For any conservative records U and V and any n, the linear map applied to the encoded increment V has the declared mass, momentum and energy components. This identity of total expressions extends to zero density. The nonzero-density derivative theorem supplies its differential interpretation. |
| `J.hasFDerivAt_zeroArea` · PhysicalJacobian.lean:177 | For every γ and every coordinate state, including vacuum, the zero-face flux is identically zero as a function of state. Its Fréchet derivative is the zero map. The proof uses M1’s `physicalFlux_zero` and takes no unit normal at zero area. |

For an independent algebraic check, put q = u·n, b = n·δm − qδρ and δp = (γ−1)(δℰ − u·δm + |u|²δρ/2). Differentiating M1 gives mass increment n·δm, momentum increment qδm + ub + nδp, and energy increment q(δℰ+δp) + Hb with H = (ℰ+p)/ρ. The program in `checks/Formula.py` checked all five components symbolically. Admissibility and γ > 1 determine the physical interpretation. A finite-function norm in the chart poses no conflict with the separately defined Euclidean face area. [Coordinate definitions](https://github.com/rois1995/CFD_Lean/blob/3788009de306d80e002976e66ba2b1103e2dbd83/CFDLean/Core/Coordinates.lean#L11) · [Flux and linear map](https://github.com/rois1995/CFD_Lean/blob/3788009de306d80e002976e66ba2b1103e2dbd83/CFDLean/Core/PhysicalJacobian.lean#L32)

## Audit findings

**Medium · The checker validates a binding’s existence, while scientific coverage still requires an independent comparison.** At `scripts/verify.py:30–49,56–64` the list of result IDs is checked against the contract, but the declaration list, stage and expected hashes are read from the candidate’s own JSON. The verifier checks that a promised name resolves to a safe theorem root. It does not compare its proposition with a previously approved type. An external in-memory fixture replaced the M2-J binding with the existing theorem `CFDLean.Coordinates.area_zero`; the ID and promise checks both accepted that substitution. None of the eight real bindings suffers this defect. The approved contract bytes match the approval revision; the six initial binding names are retained, with `jacobian_action` and `hasFDerivAt_zeroArea` added. For subsequent checkpoints compare bindings to the approved revision and inspect type changes. Executable expected-type checks are a practical option for stable interfaces. This is a limitation of future unattended sign-off.

**Low · Replay success alone does not assert equality of generated audit evidence.** `scripts/reproduce.sh:51–56` records the diff, excludes the evidence directory from its general diff assertion, and separately checks the source checksum manifest. Compare the regenerated audit JSON and inventory log to the submitted originals when making a repeatability claim. An explicit comparison in the script would make that claim self-checking. A different build transcript is expected from a cold build.

**Inventory and trust.** `KernelAudit.lean:17–57` first selects imported project modules by owner. It includes safe checked-kernel constants as roots, logs metadata-only names separately, and rejects safe local axioms. The union traversal at lines 59–75 resolves references, checks safety and inspects axiom leaves. The accepted foundations are propositional extensionality, classical choice and quotient soundness. Unreachable unsafe auxiliaries are still visible. Their empty per-row axiom field means that the non-root was skipped by the per-root axiom query. It does not certify executable code. Python rejects repeated qualified declaration records, and checks module coverage against the project's files. The eight submitted unit tests exercise parser, name coverage and foundation checks; the actual rebuild and reviewer checks provide the kernel evidence.

## Preservation and replay

The reviewer reconstructed the detached candidate from authenticated Git objects, verified its full commit hash and tree `de6ee97fdcd4b33fb7e58ffcc31a4222ab870475`, and started with a clean directory and no `.lake`. The checkpoint retained all candidate blobs. The accepted State, PhysicalFlux, Integrity and M1 specification files match their M1 Git blobs. The umbrella `CFDLean.lean` export now imports PhysicalJacobian, which imports Coordinates and then PhysicalFlux. The toolchain file, Lake configuration and manifest each match M1. The pinned mathlib revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The worker’s archived evidence hashes were checked separately before comparison.

The reviewer used the Linux x86-64 Lean 4.19.0 release compiler, Lake 5.0.0, Git 2.52.0, Python 3.12.14, Node 24.22.1 and npm 11.9.0. The supplied procedure first checks committed source hashes, fetches each of nine pinned source trees, sets both cache controls, and builds the ProofWidgets JavaScript target locally. The review did not modify candidate sources.


**Independent results.** The published command exited 0. All 24 source checksums passed before and after the build, and the eight Python fixtures passed. The regenerated verification JSON and kernel log matched both the candidate and the worker checkpoint byte for byte. Only `evidence/build.log` changed. Each of the nine dependency HEADs matched its pin and its tracked source was clean.

The six project modules contributed 167 qualified inventory records. Of these, 118 are safe mathematical roots (69 theorem records, 43 definitions, two inductives, two constructors and two recursors). The other 49 comprise 28 unsafe definitions, seven unsafe axiom-kind compiler auxiliaries and 14 metadata-only names. A separate finite-sum and continuous-linear-projection control generated the same families of unsafe specializations. No explicit axiom, unsafe declaration or unfinished proof occurred in the reviewed mathematical sources.

An independent Lean traversal checked types, values including opaque bodies, inductive constructors, and recursor rules. It reached the same 13,897 constants and precisely `propext`, `Classical.choice` and `Quot.sound`, with zero unsafe constants reachable. Fresh Lean checks used the eight bound theorems at the expected types; the derivative checks name M1's flux directly. The five historical M1 integrity examples also elaborated under the reviewer's earlier named copies. An isolated negative control imported a foreign test axiom and used it in a project-owned theorem. The actual audit rejected that theorem by its qualified name and reported the offending dependency. All fixture files were external to the candidate.

**Commands.** From the clean candidate root with the pinned toolchain on PATH, the principal replay was:

```bash
bash scripts/reproduce.sh 3788009de306d80e002976e66ba2b1103e2dbd83 ../logs/replay
```

The bundle includes the original reviewer programs in `checks/` and the successful independent logs in `logs/`. The post-replay scripts assume the candidate checkout, reviewer-only checks, logs, and the worker's archived replay (named `submitted`) occupy sibling directories. `PostReplay.sh` checks types, independently walks dependencies and compares evidence. `Negative.sh` performs the isolated forbidden-axiom test. The empty `expected-types.log` is the normal output of successful Lean examples. The replay used the official release compiler; a bootstrap audit of the compiler itself is outside this verdict.

**Next checkpoint.** Record this acceptance and proceed to the approved M2b obligations for averages, the secant identity and the equal-state limit. Carry forward the eight M2-J types when reviewing the combined J/A/R/L candidate. Details are in `Next_Steps.md`.
