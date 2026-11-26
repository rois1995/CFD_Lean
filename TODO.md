# TODO

Status date: 2026-11-26. Toolchain: Lean v4.36.0, Mathlib v4.36.0 (since MC-T, merged to `main` at 497b356).

## Implementation side (new mathematics)

1. **M5 acceptance.** The M5 lumped explicit Euler step waits for its independent implementation review
   (`reviews/M5/Reviewer_Prompt.md`). The review refers to the v4.19 commit; its theorems are unchanged in the v4.36
   port (`specifications/MC-port-types.json`).
2. **Burgers (scalar finite-volume line).** Standing authorization: `specifications/Burgers-B1-approval.md`.
   - B0 (composable core): merged (PR 2). Independent review pending.
   - B1 (TVD and bounds of the first-order Rusanov step under CFL): contract frozen (PR 3), implementation in
     `references/Burgers-B1.md`. Independent review and human review of the trusted statements pending.
   - B2 (SSP Runge-Kutta composition, multi-step bounds and TVD): contract frozen by the agent, implementation in
     `references/Burgers-B2.md`. Reviews pending.
   - B3 (MUSCL reconstruction, minmod-region limiters, TVD and bounds with Euler/SSPRK2/SSPRK3): contract frozen by
     the agent, implementation in `references/Burgers-B3.md`. Reviews pending.
   - B4 (entropy certificates, semidiscrete cell entropy inequality, Rusanov entropy stable for the square entropy):
     contract frozen by the agent, implementation in `references/Burgers-B4.md`. Reviews pending.
   - E0 (array kernel generic in its arithmetic, refinement to the scheme with real numbers, native program
     `lake exe burgers1d` with `Float`): contract frozen by the agent, implementation in `references/Burgers-E0.md`.
     Reviews pending.
   - E0b (MUSCL array kernel, `burgers1d --muscl`, refinement and transfer of the B3 results): contract frozen by
     the agent after the user chose the milestone, implementation in `references/Burgers-E0b.md`. Reviews pending.
   - Next: B5 (paper correspondence; the user must choose the references), E1 (floating point: needs a formal model
     of `Float`), E2--E4 (parallel, GPU, MPI; design notes in `references/Burgers-E0.md`).
   - Ideas not started: fully discrete entropy inequality, adapter from the periodic scalar operator to
     `CFDLean.Num.antisymmetric_pairFlux`, limiters outside the minmod region (MC, superbee), a sharp CFL constant for the bounds (B1)
     and for MUSCL (B3), accuracy statements.
   - Open for the user: the trusted B0 statements do not state the assembled `ZMod N` scheme (B0-S).
3. **Discretization/geometry generalization (cross-cutting).** The current Burgers line is a periodic, uniform-cell,
   cell-centered finite-volume specialization; the Euler/median-dual line already provides a distinct node-centered
   dual-control-volume realization. Preserve both as realizations of common numerical ideas rather than choosing one
   storage/discretization convention as the library-wide model.
   - **Non-uniform 1D finite volumes:** introduce explicit cell geometry (cell measure/length, centroid, left/right
     faces and face-to-centroid distances) and generalize the scalar finite-volume operator from one global `dx` to
     cell-dependent volumes. The natural conserved quantity becomes the volume-weighted sum
     `sum_i volume_i * u_i`; prove conservation by interface-flux cancellation.
   - **Geometry-aware reconstruction:** do not obtain non-uniform MUSCL merely by replacing `dx` with `dx_i`.
     Reconstruct slopes from distance-normalized neighboring differences and evaluate the reconstruction at the
     actual face offsets from the cell centroid. Recover the present uniform-grid `± slope/2` formulas as a
     specialization.
   - **Stability on non-uniform grids:** reformulate CFL, bounds and TVD hypotheses with local geometry/volumes and
     determine which existing B1--B3 generic lemmas survive unchanged versus which require weighted/generalized
     statements. Do not claim the present uniform-grid CFL constants for non-uniform meshes.
   - **Cell-centered vs node-centered:** keep the mathematical interfaces agnostic where possible. The scalar
     cell-centered periodic operator and the Euler node-centered median-dual operator should eventually share
     generic flux/conservation/entropy concepts through adapters, without pretending their reconstruction and
     geometry are identical.
   - **Control-volume abstraction:** investigate a common oriented-CV interface exposing owned degree of freedom,
     control-volume measure and oriented interfaces/neighbours. It should be rich enough to instantiate both a
     1D primal cell and a node-centered median-dual CV, while leaving reconstruction method-specific.
   - **Boundary conditions:** separate physical BC semantics (e.g. prescribed state/inflow, slip wall, symmetry)
     from their discrete realizations. Cell-centered FV may use exterior/ghost states and face numerical fluxes;
     node-centered dual FV uses boundary patches/transfers; FEM may use weak boundary terms. Prove each realization
     implements the intended physical BC instead of forcing one universal discrete BC API.
   - **Execution consequence:** later array/parallel/GPU/MPI refinements should target the same abstract scheme
     semantics through representation/refinement relations. Geometry, ownership and halos belong in the execution
     refinement layer, not in the PDE-level definition.
   - **Executable usability (later):** add configurable snapshot output (step- or time-based) in addition to
     diagnostics/final `--dump`, so actual solution fields can be post-processed without changing the verified
     mathematical kernel.

4. **M6 composition** (original roadmap in `specifications/M2-proposal.md`): multi-step evolution on top of M5.
5. **Fold paper 1 into CFD_Lean: done** (MR-2): `CFDLean/Papers/JST1/`, namespace `CFDLean.JST1`, on `CFDLean.Num`;
   92 statements equal the JST dumps up to namespaces (`evidence/JST1/fold-diff.md`); 37 proofs delegate to MC-N.
   The paper's own Euler definitions are linked to M1 by P5 item 20 (state map, pressure, admissibility, velocity,
   primitive map, flux; differences listed in `specifications/JST1/P5.md`).
6. **Paper-1 items: P4 done** (branch `jst1-work`, candidate): `prop:wallJST`, the Taylor parts of
   `prop:consistency`(b),(c), the PDE form of `prop:sstpde`, the Hessian form of `lem:sstentropy` (13 statements,
   `specifications/JST1/P4.md`; 105 JST1 theorems in total). Still open: mixed cells that are not affine images of the
   reference cells (trilinear hexahedra); `∫_T φ_i = |T|/(d+1)` (simplex integration; sketch in
   `specifications/JST1/P5-proposal.md` §4); paper gaps G5-G7 for the paper session.
   **P5 done** (7 statements, 112 JST1 theorems): the Ismail-Roe flux is smooth near the diagonal and P4-16.2 holds
   for it (G6, Lean side), and the bridge to M1 (item 20).
7. **SU2 correspondence** (excluded so far): relate the Lean scheme to the SU2 C++ implementation.

## Refactoring side (no new mathematics)

1. **MC-N, numerical core: done** (37 theorems in `CFDLean/Num`, `specifications/MC-N-results.json`). Open: narrow
   `CFDLean.Num.Basic`'s `import Mathlib`; move the remaining generic JST results (P1-5.4b, P1-5.8).
2. **MC-C, theorem catalog: done** (`catalog/theorems.json`, 472 theorems with B0-B4, E0, E0b and JST1; `catalog/README.md` generated by
   `scripts/catalog.py`; verifier checks coverage). Keep it updated with every new milestone (Burgers B0, M6).
3. **JST switch:** superseded by MR-2. JST_Paper_Lean becomes an archive pointing to `CFDLean/Papers/JST1/` (open:
   add the pointer note there); no further development in it.
4. **Library layout: done** (MR-1/MR-2/MR-3, `specifications/MR.md`): layered folders with a hash-pinned path map
   (MR-1), paper 1 in `CFDLean/Papers/JST1/` (MR-2), verifier generalization (MR-3).
5. **Proof validation routine:** the three validation levels are in the README ("Validation levels"): Level 1 on
   every commit (`lake build`, `scripts/verify.py`, fixtures, `sha256sum -c evidence/SHA256SUMS`); Level 2 before a
   merge to `main` (AI statement review of changed statements, `lake comparator` for Burgers B0 and JST1); Level 3
   optional and only on request (`lake check --paranoid`, run alone, overnight, 10-20 GB RAM per checker).
6. **Verifier: done** (MR-3): pretty and raw types (`pp.notation false`, `pp.coercions false`) of all promised
   theorems pinned in `evidence/raw-types.json` (v4.36 base; the v4.19 history has no raw types); the M2/M3/M4
   inherited-type checks are one table-driven check (`INHERITED` in `scripts/verify.py`), fixture-tested against the
   former functions.
7. **Housekeeping:** update the local `main` checkout to v4.36 (new `.lake`), remove merged worktrees
   (`core-v436`), shorten the README (history sections into `references/`).
