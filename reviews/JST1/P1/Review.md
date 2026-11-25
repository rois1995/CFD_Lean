# Independent review of P1 (paper 1, items 1-5)

- Reviewed: branch `p1-spec`, commit `b54607c`. Paper: frozen `LEAN_HANDOFF_PAPER1/paper1.tex` (`sha256sum -c SHA256SUMS`: OK).
- Reviewer: independent agent. It did not write the formalization. Nothing outside `reviews/P1/` was edited.
- Files of this review: `reviews/P1/Review.md` (this file) and `reviews/P1/NonVacuity.lean` (compiles with
  `lake env lean reviews/P1/NonVacuity.lean`, no errors, no `sorry`).

## Verdict: **Accept with conditions**

All 36 frozen statements build, are bound to their proofs, and use only `propext`, `Classical.choice`, `Quot.sound`. I
found no unfaithful definition, no wrong sign or constant, and no vacuous statement. The conditions are about what the
claim "checked in Lean 4" covers (S1, S4) and about the integrity script (S2, S3). None of them needs a change to a
frozen statement.

## 1. Reproduction

| Check | Result |
|---|---|
| `./scripts/check.sh` (LEAN_NUM_THREADS=2, nice 19) | exit 0; "theorems with standard axioms only: 36 of 36"; "OK" |
| Frozen hashes (`P1-frozen.sha256`, 15 files) | all OK; `git diff e3f6a11 HEAD` on these files: no change |
| Forbidden tokens (sorry, admit, axiom, native_decide) | none |
| Other escape hatches (`unsafe`, `implemented_by`, `extern`, `opaque`, `macro`, `elab`, `run_cmd`, `debug.*`, attributes) | none in `NumCore`, `Paper1`, `KernelAudit.lean` |
| Heartbeat raises | one: `Paper1/Proofs/DualFacets.lean:18`, `maxHeartbeats 2000000` for `rot_eq` (known) |
| Other `set_option` | `linter.unusedSectionVars false` in `Closure.lean:11`, `DissGeom.lean:7` (harmless) |
| Fresh re-elaboration `lake env lean KernelAudit.lean` (not the replayed Lake log) | 36 × `[propext, Classical.choice, Quot.sound]` |
| Bindings | every `theorem p1_x_y : Spec.P1_x_y` exists in the file named in `P1-results.json` (36/36); `KernelAudit.lean` has `example : Paper1.Spec.P := Paper1.Proofs.p` for all 36 |
| Pins | `lake-manifest.json`: cfdlean `3a586a4…` (= approval record), mathlib `c44e0c8…`; checked-out packages at those revisions; toolchain v4.19.0 |
| `warningAsError = true` in `lakefile.toml` | yes |

## 2. Non-vacuity checks (`reviews/P1/NonVacuity.lean`)

- `rest_admissible`: for every `d` and `Gas`, the state ρ = 1, m = 0, E = 1 is admissible (hypothesis of P1-1.x, 2.0,
  2.5, 4.3b).
- `diamond`: a valid 2D mesh of four right triangles around the origin. Proved: `diamond.Valid`; the P1 gradients;
  `diamond.Closed 4` (the centre vertex is closed); `¬ diamond.Closed 0` (a boundary vertex is not closed, so `Closed` is
  not trivially true); and P1-5.4 at the centre gives `tr G(ν) = 4 V_4`. So the `Closed` hypotheses of P1-2.3, 5.3 and
  5.4 can be met in a real 2D mesh.
- `line`: a valid 1D mesh of two segments. Proved: `line.FacetPaired 1` (explicit pairing), then `line.Closed 1` through
  `p1_5_0a`. So `FacetPaired` can be met.
- Not done: a CFD_Lean mesh with an interior vertex (P1-5.0b). CFD_Lean proves `oneCell_conforming` and
  `two_cells_conforming`, but in both meshes every vertex is on a boundary face. The `Controls`/`TwoCells` modules are
  not built in this package, so I did not re-check them here. The interior case of P1-5.0b is satisfiable in principle
  (e.g. 8 tetrahedra around a centre point), but no concrete witness exists.
- The other hypotheses are easy to meet (`0 < π`, `0 < λ̂`, `0 < Λ`, `w_E < 0`, `0 < V`, `0 < h`, `0 < sixVolume`).

Checks on Lean's total definitions: every division that matters is guarded. Velocity, `w` and `ψ` assume admissible
states (ρ > 0, p > 0). `viscFlux` assumes `θ = -w̄_E > 0` and `R > 0`. `nSplit` assumes `π > 0`, `psiF` assumes
`λ̂ > 0` and `Λ > 0`. `logMean`, `nuOf` and `unit` are only met where the argument is nonzero, or where the 0 value
is harmless (`e_ii = 0`, `n = 0` on uncoupled pairs). `WMesh.vert` is an embedding, so `μ_ik` (i ≠ k) counts each cell
at most once.

## 3. Statement table

Faithful = the Lean statement means what the cited paper text says, up to the differences listed in `P1.md` /
`PAPER_GAPS.md`.

| ID | Faithful? | Vacuity risk | Notes |
|---|---|---|---|
| P1-1.0 | yes | none | `U = -ρs/(γ-1)`, `s = ln p - γ ln ρ`, `w` as in the literature; `HasFDerivAt` on the sup-normed `State d` (norm-independent) |
| P1-1.1 | yes | none | Forms of lines 264-265 checked by hand: `q̃ = q + δw_E δp`, pencil `λ² - (γ+1)λ + (3γ+1)/4` |
| P1-1.2 | yes | none | Main bounds of `lem:eps2`, any `d`, any velocity |
| P1-1.3 | yes | none | |
| P1-1.4 | yes | none | λ_1.4 = 0.82583 ∈ (0.8258, 0.8259) |
| P1-1.5 | yes | none | Sign convention: production = `[w]·f_ik`, `d_ik = λε2(ũ_i - ũ_k)` |
| P1-1.6 | yes (G1) | none | "sharp" as best constants; G1 is OPEN in the paper |
| P1-2.0 | yes | none | `Q = U v`, `ψ = ρv` |
| P1-2.1 | yes | none | generic |
| P1-2.2 | yes | none | Generic `w, ψ, S`. `β_i := -Σ_k n_ik` by definition; the link to the mesh is P1-2.3 (see M1) |
| P1-2.3 | yes | none (diamond) | Any dual `W` with `Σ_a W = |T|`; `Closed → β = 0` |
| P1-2.4 | yes | none | Mostly definitional; positivity is the content |
| P1-2.5 | yes | none | Ismail-Roe 2009 formulas checked term by term (z1, z5, ρ̂, û, p̂1, p̂2, ĥ) |
| P1-2.6 | yes | none | Conservation = antisymmetry; trivial, like the paper |
| P1-2.7 | yes, weak | none | Near-tautological (S4): uniform `ũ` hard-coded as `ut0 - ut0`; boundary data `b_i = F(U)·β_i` with `β := -Σ n` is assumed |
| P1-3.1 | yes (G3, G4) | none | Extra hypothesis "uncovered pair ⇒ n_ik = 0" (needed, listed) |
| P1-3.2 | yes (G2) | none | Linearity of the means; trivial, like the paper's proof |
| P1-3.3 | yes (G2-G4) | none | Real content (homogeneity of λ̂, Ψ, Φ); `Λ` is a fixed input (closure (A), part 2) |
| P1-3.4 | content-free | — | `p = 1 → p^a c = c`. That π_ik = 1 and the counts, sums and sensor reduce on a simplex mesh is not formalized (S4) |
| P1-4.0 | yes | none | Chain rule written as a hypothesis on `G` (listed); `τ`, Stokes 2/3, `q = -κ∇T` signs checked |
| P1-4.1 | yes | none | generic, weights ω |
| P1-4.2 | yes | none | `d ≤ 3` is needed (`(tr S)² ≤ d S:S`), listed |
| P1-4.3 | yes | none | More general than the paper (`w_E < 0` instead of admissible, weights ω ≥ 0) |
| P1-4.3b | yes | none | |
| P1-4.4 | yes | none | Hypothesis `w̄_E ≠ 0` not needed (harmless, M4) |
| P1-5.0a | yes | none (line) | Sufficient condition for "interior" |
| P1-5.0b | yes | interior case not exhibited (M3) | d = 3 only; proof uses `faceMultiplicity`, `oppositeSides` of CFD_Lean |
| P1-5.1 | yes | none | `g` from the inverse edge matrix; `|f_o| n_o = -d|T| g_o` as in the proof of `prop:fv` |
| P1-5.2 | yes | none | `μ` matches `|S_ik|/(d+1)` (ω-weighted) |
| P1-5.3 | yes | none (diamond) | Global sum over ordered pairs = 2|Ω| I (paper: |Ω| I over unordered pairs) |
| P1-5.4 | yes | none (diamond) | Ordered pairs: 2d|Ω| (paper: d|Ω|); equality case as non-negative multiples |
| P1-5.4b | model | none | Abstract vectors; the box-dual area `(V/h_α) ê_α` is assumed, not derived from a mesh (M2) |
| P1-5.5 | yes | none | generic algebraic core |
| P1-5.6 | yes | none | 3D: CFD_Lean's flag-triangle `localInterface` (real geometry); 2D: midpoint-centroid segment, orientation chosen towards `k` (that is the outward normal of `C_i`) |
| P1-5.7 | yes | none | `MeshData.positive` gives nondegenerate cells |
| P1-5.8 | yes | none | |

## 4. Findings

### Blocking

None.

### Should fix

**S1. The scope of the claim "Lemmas X-Y are checked in Lean 4".** (`P1.md` lines 66-74; `PAPER_GAPS.md`.)
Some paper statements are checked only in a modified or partial form:
- `lem:splitmean`: checked only with the G2-G4 changes (sensor a fixed input, `bnd` split-independent, positivity
  assumed). The paper text still says (A) replaces "every nodal quantity", and G2-G4 are OPEN.
- `lem:eps2`: "both bounds are sharp" is checked as best constants (G1, OPEN).
- `prop:consistency`: only (a), with the closure's free-stream property as a hypothesis.
- `lem:dissgeom`: only (a)-(c), not (d). "Interior vertex" is `Closed`. For d = 3 it follows from CFD_Lean's
  conforming predicate. For d = 2 there is no theorem from a conforming triangle mesh, only from `FacetPaired`.
- `prop:fv`: real geometry for d = 2, 3 only.

Fix: fix G1-G4 in the paper first, or write the sentence with these qualifiers, for example: "Lemmas eps2, ec,
splitmean (with hypotheses …), dissgeom (a)-(c), Theorem visc and Propositions fv (d = 2, 3) and consistency (a)
(closure assumed) are checked in Lean 4 (repo, commit b54607c)."

**S2. The integrity check does not cover the pins.** (`scripts/check.sh:7`, `specifications/P1-frozen.sha256`.)
P1-5.0b, 5.6 and 5.7 are stated with CFD_Lean definitions (`MeshData`, `Conforming`, `faceCount`, `localInterface`,
`sixVolume`, `volume`). All statements depend on Mathlib. `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are
not hashed and not checked. A pin change would change the meaning of frozen statements, and `check.sh` would still pass.
Fix: add these three files to the checked hashes, or have `check.sh` check the manifest `rev` of `cfdlean` and
`mathlib` against the approval record. Either way, add an approval entry.

**S3. The bindings in `KernelAudit.lean` are not cross-checked.** (`scripts/check.sh:18`.) The count of 36 comes from
the `#print axioms` lines, not from the `example : Spec.P := Proofs.p` lines. If a binding line were deleted, or bound
to a different name, the script would still pass. The risk is low, because each `theorem p1_x_y` already has type
`Spec.P1_x_y`. Fix: in `check.sh`, for every entry of `P1-results.json`, grep for the exact line
`example : <statement> := <theorem>` in `KernelAudit.lean`. Also check that the 36 IDs in `P1.md`, the JSON and
`KernelAudit.lean` are the same set.

**S4. Trivial statements are listed as if they had content.** (`P1.md` index rows P1-3.4 and P1-2.7.)
- P1-3.4 (`Paper1/Spec/Item3.lean:40-42`) is `p = 1 → p^a * c = c`. It does not check "on a simplex mesh
  (splitmean) is (jst)": it does not show that π_ik = 1, that `n_i = |E(i)|`, or that the π-weighted sums reduce.
- P1-2.7 (`Paper1/Spec/Item2.lean:70-79`) hard-codes the uniform `ũ` as `ut0 - ut0`. It assumes `b_i = phys U (β_i)`
  with `β_i := -Σ_k n_ik`, so after consistency and linearity it is a tautology.

Fix (documentation only, no statement change): mark them in `P1.md` as "trivial consistency check". Do not count them
as checked content of `lem:splitmean` / `prop:consistency`. Optionally, a later item could state P1-3.4 on a `WMesh`
whose splits are the cell itself (π = 1 on every edge).

### Minor

- **M1.** `β_i` is the discrete `∫∇φ_i = Σ_T ω|T| g_i` (`NumCore/WMesh.lean:40`), not the paper's `∮ φ_i N`. They are
  equal by the divergence theorem, which is not formalized. Write this in `P1.md` next to P1-2.2/2.3.
- **M2.** P1-5.4b (`Paper1/Spec/Item5.lean:56-63`) is a model on abstract vectors. The box-dual area vectors
  `±(V/h_α) ê_α` are inputs, not derived from a Cartesian mesh. The docstring says "Cartesian model"; `P1.md` should say
  so too.
- **M3.** No concrete witness for the interior case of P1-5.0b (see section 2). Optional: add a reviewer-style
  non-vacuity file to the repo, e.g. the 2D diamond of `reviews/P1/NonVacuity.lean`, a 2D `FacetPaired` example, or a
  3D octahedron that satisfies `Conforming`.
- **M4.** Unused or unneeded hypotheses (harmless; the statements are a little weaker than they could be):
  - `wb .energy ≠ 0` in P1-4.4 (`Item4.lean:48`);
  - `∀ s, 0 ≤ ω s` in P1-3.3 (`Item3.lean:34`; `_hω` in `Proofs/Item3.lean:94`);
  - `M.Valid` in P1-2.3 (`_hM` in `Proofs/MeshAlgebra.lean:58`);
  - `M.Valid` in P1-5.0a (`_hV` in `Proofs/Closure.lean:174`).
- **M5.** There is no theorem that composes P1-2.5 into P1-2.2 (Ismail-Roe with `S` = admissible states). It is easy,
  but the paper's example "e.g. the Ismail-Roe flux" is checked only as two separate facts.
- **M6.** `P1-results.json` has no commit, toolchain or axiom fields. The forbidden-token regex in `check.sh:9` only
  catches `axiom` at the start of a line (e.g. not `private axiom`). Both are covered in practice by `#print axioms`.
  Adding the commit and toolchain to the JSON would make the record self-contained.
- **M7.** The heartbeat raise in `DualFacets.lean:18` (2M) is reported by `check.sh`. It is acceptable.
- **M8.** Side note on `PAPER_GAPS.md`: G1-G4 are OPEN. The approval record says the solver session accepted the
  answers. The paper still has to change before S1 can be dropped.

## 5. What I checked by hand against the paper

- Definitions:
  - entropy `U = -ρs/(γ-1)`, `s = ln(pρ^-γ)`;
  - entropy variables `((γ-s)/(γ-1) - ρ|v|²/(2p), ρv/p, -ρ/p)`;
  - `ũ = u + p e_E = (ρ, ρv, ρH)`;
  - the Euler flux;
  - `ψ = ρv`, with `Q = Uv`;
  - the Ismail-Roe flux;
  - `λ_γ, Λ_γ` and the pencil;
  - P1 gradients from the inverse edge matrix (`φ_{β+1}(x) = (E⁻¹(x - x_0))_β`);
  - `|T| = |det|/d!`, `m_T = |T|/(d+1)`;
  - the median-dual `c_ik = Σ ω m_T g_k`, `n = c - cᵀ`, `B = c + cᵀ` (boundary mass matrix: `Σ_T m_T(g_i+g_k) =
    ∫∇(φ_iφ_k)`, so `Closed` is exactly "row i of `B_c` vanishes"), `V`, `μ`;
  - `ν = (n·e/|e|²) e`;
  - `G_i(y) = Σ|y||e| ê⊗ê`;
  - `viscFlux` (θ = -w_E, `∂v = (G_m - v⊗G_θ)/θ`, `∂T = -G_θ/(Rθ²)`, `τ = μ(∂v+∂vᵀ) - (2/3)μ(div v)I`, flux
    `(0, τ, τv + κ∇T)`);
  - the 2D dual segment (midpoint to centroid, rotated, oriented towards k);
  - the 3D flag triangles (CFD_Lean).
- Sign conventions: production `-Σ_i w_i·Σ_k F_ik`; `R^v_i = -Σ ω|T| F g_i`; FV residual `Σ F·S` with
  `S = m_T(g_k - g_i)`, outward from `C_i`.
- Pair-count conventions: the ordered sums in P1-5.3/5.4 are twice the paper's unordered sums, consistently.
