# MC-T type map (v4.19 to v4.36)

Source: `evidence/port-types.json`. The accepted type comes from `be20e81:evidence/verification.json`. The current type
is the `type` field that `KernelAudit.lean` prints on Lean v4.36.0 with Mathlib `fc4f59e5`. The 199 promised theorems
are the M2-M5 bindings, selected with the stage filter that `scripts/verify.py` uses.

| Class | Count |
|---|---|
| identical | 191 |
| notation | 5 |
| mathlib-rename | 3 |
| pretty-printer | 0 |
| other | 0 |

## Non-identical items

- `CFDLean.Assembly.residual_outgoing` (notation): `∑ e ∈ {e | p e}, f e` now prints as `∑ e with p e, f e`. Both are `Finset.sum (Finset.filter p univ) f`.
- `CFDLean.Time.mesh_amount_used` (notation): `∑ i ∈ Finset.filter M.Used Finset.univ, …` now prints as `∑ i with M.Used i, …`. The term is the same.
- `CFDLean.Roe.operator_B` (notation): `(…).comp (B γ z)` now prints with Mathlib's infix `∘SL`, which is `ContinuousLinearMap.comp`.
- `CFDLean.Roe.roeMatrix_B` (notation): `.comp` now prints as `∘SL`. The term is the same.
- `CFDLean.Roe.roeMatrix_CB_inverse` (notation): `.comp` now prints as `∘SL`. The term is the same.
- `CFDLean.Roe.Spectral.exists_tangent_basis` (mathlib-rename): Mathlib renamed `Basis` to `Module.Basis`.
- `CFDLean.Roe.Spectral.roe_absolute_basis` (mathlib-rename): Mathlib renamed `Basis` to `Module.Basis`.
- `CFDLean.Roe.Spectral.roe_convective_tangent_span` (mathlib-rename): Mathlib renamed `Basis` to `Module.Basis`.

## Identical strings that needed a source change

- `CFDLean.PhysicalJacobian.jacobian_action`: Lean core now rewrites nondependent `let` in a theorem type to `have`
  (option `cleanup.letToHave`). Without a fix the type would print `have u := …`. The theorem now has
  `set_option cleanup.letToHave false in`, so its type keeps the `let` binders, as in v4.19.
- `CFDLean.Roe.operator_B` (and `midpoint_velocity`, which is not promised): the statement writes `z i.succ` with
  `i : Fin 3`. In v4.19 this elaborated to `z ↑↑i.succ` (Fin 4 to ℕ to Fin 5) through the global `NatCast (Fin n)`
  instance. That instance is now scoped (`Fin.NatCast.instNatCast`), so the statement is preceded by
  `open Fin.NatCast in`. The term is still `Nat.cast (Fin.val i.succ)`, and the value is still `a % 5`
  (old `Fin.ofNat' 5 a`, new `Fin.ofNat 5 a`).
- `CFDLean.pressure_toConservative`: the hypothesis `hρ` is no longer needed by the proof (the new `field_simp` closes
  the goal without it). The unused-variable linter therefore fails under `warningAsError`. The statement is kept
  unchanged, with `set_option linter.unusedVariables false in`.

## Non-promised statements

- `CFDLean.MedianDual.Controls.shared_triangle`: the hypothesis `upperRegion x` (a `Set` applied as a function) no
  longer elaborates and is now written `x ∈ upperRegion`. This is definitionally the same proposition.
- The following types differ only in notation: `convective_eq_kernel` (`LinearMap.ker f` now prints as `f.ker`),
  `minus_range`, `plus_range` and `rank_one_range` (`Submodule.span ℝ {r}` now prints as `ℝ ∙ r`), `amount_used`
  (filter `with`), and `absolute_basis_representation` and `convective_tangent_span` (`Module.Basis`).
