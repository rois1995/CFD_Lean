# P6 proposal: the simplex integral `∫_T φ_i = m_T`

Written 2026-11-26. Same process as P4-P5. Paper input `Handbook/paper1/paper1.tex`, sha256 `5ec5f9db…` (results section changed during the session; no
statement affected).
P1-P5 stay frozen; P6 only adds files. The user chose this batch (option 1 after P5) under the standing authorization
of the whole cycle.

## 1. Item

| # | Paper | What | Size |
|---|---|---|---|
| 21 | `prop:consistency`(b) (line 285), proof line 975 (old 946) | `∫_T φ_i = m_T`; the Galerkin form `Σ_k ½(F_i+F_k)·n_ik = ∫_Ω φ_i ∇·F_h` with a real integral | M-L |

It closes decision D1 of `P4-proposal.md` (P4-16.1 stated everything but the integral).

## 2. Statement sketches

- **P6-21.1.** For a nondegenerate simplex `T`: the convex hull of the vertices is `{x : φ_b(x) ≥ 0 ∀ b}`, and its
  Lebesgue measure is `T.vol = |det(x_β - x_0)|/d!` (the library's algebraic volume).
- **P6-21.2.** `φ_b` is integrable on the hull and `∫_T φ_b = T.vol/(d+1)` (= `m_T` of the median dual).
- **P6-21.3.** On a valid mesh at a closed vertex: `Σ_k ½(F_i+F_k)·n_ik = Σ_T ω_T ∫_T φ_i ∇·F_h`, with `F_h` the P1
  interpolant and `∇·F_h` defined by derivatives (not by the constant formula).

## 3. Decisions (self-decided; reason given)

- **D1 — region.** The closed simplex is `convexHull ℝ (range T.x)` (the textbook definition); 21.1 also gives the
  barycentric description, which the proofs use.
- **D2 — measure.** `volume` on `Vec d = Fin d → ℝ` (Mathlib's product Lebesgue measure). Not Mathlib's
  `Affine.Simplex.volume` (height formula on Euclidean spaces): the library's `T.vol` is the determinant formula, and
  21.1 ties it to the Lebesgue measure directly.
- **D3 — weights.** 21.3 keeps the mesh weights `ω_T` of `WMesh` (1 on simplex meshes, split weights on mixed meshes),
  as P4-16.1.
- **D4 — proof route (not part of the statements).** `T = A(Δ)` with `A t = x_0 + E t`, `Δ = {t ≥ 0, Σt ≤ 1}`;
  `|Δ| = 1/d!` by induction (Fubini on `ℝ × ℝ^d`, scaling); `|T| = |det E||Δ|` (Haar measure under a linear map);
  `∫_T φ_a = ∫_T φ_b` by the affine involution of `T` that swaps vertices `a` and `b` (its linear part `L` has
  `L² = I`, so `|det L| = 1`); then `Σ_b φ_b = 1` gives each integral `|T|/(d+1)`.
