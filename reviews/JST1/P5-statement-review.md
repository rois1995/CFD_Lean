# P5 statement review (items 19-20)

Independent reviewer: one fresh agent (Opus, high effort), 2026-11-26. It received the paper lines (95-110 entropy and
fluxes, 150-158 `lem:ec`, 282-298 `prop:consistency`, 938-955 its proof), the two statement files
(`Spec/Item19.lean`, `Spec/Item20.lean`) and the definitions they use (log mean, paper Euler, Ismail-Roe, M1 Euler,
P4-16.2), but not the author's opinion. Read-only review; one `lake env lean` run on a scratch copy (elaboration,
`pp.fullNames`, name-capture check; it proved P5-20.1..20.4 there by `rfl`/`simp`) and a Python check of the
Ismail-Roe flux (2D, γ = 1.4): consistency to 1e-16, Tadmor's condition to 1e-15, (F^IR - mean)/|Δu|∞² between 1.0 and
1.5 for |Δu| = 1e-1, 1e-2, 1e-3.

**Verdict: no BLOCKING finding**; all six statements true, faithful, non-vacuous; no name capture (all names bind to
`CFDLean.JST1.*`, `Vec` to `CFDLean.Num.Vec`; M1 only through `CFDLean.squareSum` and the `Conservative`/`Primitive`
fields).

## Findings and follow-up

| # | Severity | Finding | Follow-up (before freeze) |
|---|---|---|---|
| 1 | should-fix (cosmetic) | `Item20.lean` has a `let` (P5-20.4) but no `set_option cleanup.letToHave false`. | Added the option to `Item20.lean` (kept in `Item19.lean` for uniformity). |
| 2 | minor | In 19.3 the O-constant depends on the fixed `y`; the scheme uses many face vectors `n_ik`. | 19.3 restated with one constant for all `y`: `∃ C, ∀ᶠ p in 𝓝 (u0,u0), ∀ y, ‖F^IR - mean‖ ≤ C‖y‖‖Δu‖²` (stronger; proved from the per-basis-vector big-O and the linearity in `y`). |
| 3 | minor | 19.3 is local; "on each pair" needs one constant on a compact set of states. | Docstring note (compactness gives it; not stated). |
| 4 | minor | 20.4 is a definitional unfolding. | Accepted (bridge; recorded as bookkeeping in `P5.md`). |
| 5 | minor | `∀ n : ℕ` instead of `∞`/`ω`. | Accepted (equivalent, decision D1). |

Paper notes of the reviewer (recorded in `PAPER_GAPS.md` under G6): the O(|Δu|²) constant is only locally uniform
(compact set of admissible states, scales with |n_ik|); "expand about the midpoint" needs the segment in the admissible
set (true: the set is convex in conservative variables).
