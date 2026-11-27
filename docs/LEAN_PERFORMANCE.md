# Writing fast and safe Lean proofs in CFD_Lean

Read this before you add a proof that computes (`decide`, `decide +kernel`, large `simp`/`norm_num` case splits).
It collects what we measured on the paper-1 (JST1) proofs, in Lean's kernel and in the five external kernels of the
paranoid comparator (rule 9). All rules keep the trusted base unchanged: the statement
and the Lean kernel. A faster proof is exactly as safe as a slower one, because a wrong shortcut does not compile.

## 1. Brute force first, then optimize

Land a working brute-force proof first (a closed computation checked by the kernel). A smarter proof can replace it
later. Keep `native_decide` forbidden: it trusts compiled code; use `decide +kernel`.

## 2. Keep case splits on an inductive type out of kernel loops

This is the largest effect we found. `Kind.cell`, `refZ` and `Kind.tets` are defined by a case split on
`Kind` (`.hex`, `.prism`, `.pyr`). Inside a `decide +kernel` loop the kernel evaluates such a case split again on
every iteration; it does not share the result. Measured (hexahedron, 384 sub-tetrahedra):

| Computation | Time |
|---|---|
| `Kind.hex.tets.length = 384` (list built through `Kind.cell`) | 435 s, 6.7 GB |
| the same list built from `RefCell.hex` directly | about 2 s |
| P3 check `localOK .hex` through `Kind` (whole module `Item11cBase`, CI) | 1496 s |
| the same check with plain arguments (whole module, local) | 53 s |

Pattern: write the check once with the data as plain arguments, rewrite the original check into it by `rfl`
(cheap: the kernel unfolds the case split once), then compute.

```lean
def checkKg {n : ℕ} (C : Cell3 n) (R : Fin n → Z3) (S : Z3) (z : Fin n) : Bool := ...   -- no `Kind` inside

theorem checkK_hex : checkK .hex = true := by
  rw [show checkK .hex = checkKg RefCell.hex hexR (4, 4, 4) 0 from rfl]
  decide +kernel
```

See `CFDLean/Papers/JST1/Proofs/Item11cBase.lean` (`checkKg`, `localOKg`).

## 3. Do not re-evaluate a large set inside a quantifier

A statement such as `∀ S ∈ bdTrisOf M, P S` makes the kernel build the whole `Finset` (a `biUnion` and `filter`
over all cells) and may recurse very deeply. Test each candidate directly instead and derive the set form with a
short ordinary proof. Facts that follow from a definition (for example "a boundary triangle belongs to one cell")
are proved, not computed.

Keep `Finset` out of the kernel loop altogether when its elements come from `List.toFinset`: even
`∀ p ∈ blockFT 0, 13 ∈ p.1 ∨ True` (with `p.1` a `toFinset`) fails with kernel deep recursion, on CI and locally.
Compute on the lists as one `Bool` (`List.all`, `List.any`, `List.contains`, and set equality as
`∀ x, l.contains x == l'.contains x`), check it with `decide +kernel`, and move the result to the `Finset`
statement with `List.mem_toFinset` (P8: `blockFL`, `chk13B`, `chk_13L`, `not_bdF` in `Item23Conf.lean`). A
`Finset` built with `insert` (`{a, b, c}`) did not show the problem (`chk_13` in `Item23Sum.lean`). Probe a
suspect form in a scratch file first: the failure shows in seconds.

## 4. Never raise `maxRecDepth` to get past a kernel "deep recursion" error

On 2026-11-26 a check with `maxRecDepth 100000` grew to 55 GB; the operating system killed it together with the
desktop application. Reformulate the check (rules 2-3). Raising `maxHeartbeats` locally for a closed check is fine.

## 5. Measure before optimizing

- Time one file: `lake env lean File.lean` (no project-wide file check); wrap it in `/usr/bin/time -f "%M kB %e s"`.
- Split a slow computation into tiny `decide +kernel` lemmas (list length, one case, one iteration) in a scratch file
  and time each; the slow step is usually one definition, not the size of the loop.
- After switching branches, `lake build` first re-checks thousands of files (disk-bound, low CPU); that is not Lean.
- CI times per module: `gh run view <run> --log | grep "Built CFDLean"`.
- External kernels: see rule 9. A fast Lean build does not mean a fast comparator run.

## 6. Run Lean under a memory cap

```bash
LEAN_NUM_THREADS=2 systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 nice -n 19 lake build ...
```

One Lean process at a time on a shared machine. If a check hits the cap, only that process stops.

## 7. Put large closed checks in their own module

`lake` saves each finished module, so an interrupted build loses only the running module, and CI can build
independent modules in parallel (the JST1 P8 proofs, on their own branch, use `Item23Base`, `Item23Conf`,
`Item23Sum` and `Item23`).

## 8. Smaller pitfalls

- `Fin Kind.hex.n` is not syntactically `Fin 8`. Numerals at type `Fin Kind.hex.n` fail (`OfNat`), and `rw` can fail
  with a motive that is not type correct. State helper lemmas at `Fin 8`, write `@List.getD (Fin 8) …`, and combine
  with term-mode `Eq.trans`/`congrArg₂` instead of `rw`.
- Inside `first | … | …`, use `ring1`: `ring` does not fail when it cannot close the goal (it falls back to
  `ring_nf`), so `first` never tries the next branch.
- `congr` on a sum over a big index type can recurse very deeply; use `refine congrArg (fun z => …) ?_`.
- `decide` needs one decidable instance for the whole statement; very large statements can fail instance search.
  Split them into several lemmas.

## 9. Keep each closed check small for the external kernels

`lake comparator --paranoid` re-checks every proof with five external kernels (`leanchecker-paranoid`, `lean4lean`,
`nanoda`, `con-leche`, `con-ron`). They evaluate `decide +kernel` computations much more slowly than Lean's kernel,
and their memory grows with the work done in one declaration. Measured on JST1 (2026-11-27):

- `con-ron` needs about 0.1 GB per second of work in one declaration; the memory is freed after the declaration.
  A check that takes 55 s in `con-ron` peaked at 10.8 GB. The GitHub runner has 7.6 GB and the checkers run two
  workers, so two such checks at once swap, and `con-ron` ran for more than 4 h instead of 8 min.
- Lean's own speed is no guide: a module that builds in 20 s can hold a check that takes a minute and 10 GB in
  `con-ron`.
- Each `decide +kernel` call becomes its own auxiliary declaration (`thm._proof_1_1`, `_proof_1_2`, ...), so its
  memory is freed before the next one.

Rules:

- **Keep every closed check under about 10 s in `con-ron` (about 1 GB).** Split a large check into several
  declarations: one per cell, one per chunk of a list. `all_of_chunks` (`Proofs/Chunks.lean`) turns chunk lemmas
  `((L.drop (k * i)).take k).all f = true` back into `L.all f = true`. For a sum, prove one value per chunk and add
  the values (`intSL_append` in `Item22.lean`, `sum13_*` in `Item23Sum.lean`).
- **Remove a large shared subterm before you split.** Each piece computes it again. In P8, every face test used the
  boundary set `bdF` (a `biUnion` and `filter` over all cells). Checking only one of the 8 cells still took 33 s and
  5 GB, against 73 s and 10 GB for all 8. The fix was to stop using `bdF` in the computation (rule 3, and `mem_bdF`
  proves the set fact once by an ordinary proof).
- **Prefer lists to `Finset` in the computation.** Set equality of two short vertex lists as
  `p.all q.contains && q.all p.contains` (`sameL` in `Item23Conf.lean`), with a lemma to `toFinset` equality.
  P8 `chk_intF` went from 55 s and 10.8 GB to `intB_true` at 8 s and under 2.5 GB.
- **Write a long computed list out once.** A literal list in chunks (`hexL0` .. `hexL7` in `Item22.lean`) and one
  equality `tetsOf RefCell.hex = hexTL` by `decide +kernel` let the chunk lemmas run on fixed data. This alone
  saves little (13 %); it is what makes the chunking possible.
- `rfl` lemmas that tie a check to its fast form (rule 2) are cheap in the external kernels too.

How to measure, locally, in minutes:

```bash
B=~/.elan/toolchains/leanprover--lean4---v4.36.0/bin
lake build CFDLean.Verification.JST1Verify          # under the memory cap of rule 6
lake env $B/leanexport CFDLean.Verification.JST1Verify -- CFDLean.Verification.JST1Verify.p8_23_1 > /tmp/x.ndjson
/usr/bin/time -f "%e s, %M kB" $B/con-ron --progress=1 --jobs=1 /tmp/x.ndjson 2> ron.log
```

The export contains the named theorems and everything they use. With `--jobs=1`, the time between two
`con-ron: check` lines of `ron.log` is the check time of the second declaration, so sorting those gaps gives the
ranking. Do the same with `con-leche`. Measure the whole challenge
(`Challenges/JST1.comparator.json`, `theorem_names`) before and after a change, and add the `paranoid` label to the
PR for the run on CI hardware.

## 10. CI cost

The full build dominates the integration run (35 min before the change of rule 2, 11 min after). Integration CI
reuses the compiled modules of unchanged files from a build cache. Release verification builds from scratch and
re-checks every proof with five external checkers (`lake comparator --paranoid`), which repeats every closed
computation. Prefer the fast forms above for any new closed check.
