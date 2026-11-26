# Writing fast and safe Lean proofs in CFD_Lean

Read this before you add a proof that computes (`decide`, `decide +kernel`, large `simp`/`norm_num` case splits).
It collects what we measured on the paper-1 (JST1) proofs. All rules keep the trusted base unchanged: the statement
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

## 9. CI cost

The full build dominates the integration run (35 min before the change of rule 2, 11 min after). Integration CI
reuses the compiled modules of unchanged files from a build cache. Release verification builds from scratch and
re-checks every proof with five external checkers (`lake comparator --paranoid`), which repeats every closed
computation. Prefer the fast forms above for any new closed check.
