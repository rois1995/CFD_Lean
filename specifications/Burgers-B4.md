# Burgers B4: entropy layer (semidiscrete entropy stability)

Status: **frozen for implementation on 2026-11-26 by the agent under the standing authorization**
(`specifications/Burgers-B4-approval.md`). No human approved the statements of this contract.

Base: Burgers B0--B3 on `main` at the merge of PR 6. Toolchain: Lean v4.36.0. Exact real arithmetic.

## Purpose

B4 adds the first entropy results for the periodic first-order finite-volume operator of B0:

1. two flux certificates in Tadmor's form, entropy stability and entropy conservation, for an entropy variable `v` and
   an entropy potential `ψ`;
2. generic theorems for any flux with a certificate: a cell entropy inequality with an explicit numerical entropy flux,
   and nonpositive total entropy production on a periodic grid;
3. the Burgers instance for the square entropy `η(u) = u²/2`: the entropy-conservative flux `(a² + ab + b²)/6` and the
   proof that the Rusanov flux is entropy stable.

## Mathematics

Entropy pair `(η, q)` with `q' = η' f'`. Entropy variable `v = η'`. Entropy potential `ψ = v f - q`.
For Burgers and the square entropy: `v(u) = u`, `q(u) = u³/3`, `ψ(u) = u³/6`.

**Certificates** for a two-point flux `F`:

```text
entropy stable:        (v(b) - v(a)) F(a, b) ≤ ψ(b) - ψ(a)   for all a, b
entropy conservative:  (v(b) - v(a)) F(a, b) = ψ(b) - ψ(a)   for all a, b
```

**Numerical entropy flux** of the interface between cells `i` and `i+1`:
`Q_i = (v_i + v_{i+1})/2 · F(u_i, u_{i+1}) - (ψ_i + ψ_{i+1})/2`. For a consistent flux, `Q = v f - ψ = q` on equal
states.

**Cell entropy identity.** With `L_i = -(F_i - F_{i-1})/dx` (the B0 right-hand side):

```text
v_i L_i + (Q_i - Q_{i-1})/dx = [ (v_{i+1} - v_i) F_i - (ψ_{i+1} - ψ_i) + (v_i - v_{i-1}) F_{i-1} - (ψ_i - ψ_{i-1}) ] / (2 dx)
```

So an entropy-stable flux and `dx > 0` give the cell entropy inequality `v_i L_i ≤ -(Q_i - Q_{i-1})/dx`, and the sum
over a periodic grid gives `Σ_i v_i L_i ≤ 0`. An entropy-conservative flux gives equalities.

`v_i L_i` is the time derivative of `η(u_i)` along the semidiscrete system `u_i' = L_i(u)`. B4 states the algebraic
inequalities only; it has no time derivative and no ODE.

**Burgers.** The flux `F_EC(a, b) = (a² + ab + b²)/6` is consistent and entropy conservative. The Rusanov flux is
`F_EC(a, b) - (α/2 - (b - a)/12)(b - a)` with `α = max(|a|, |b|)`. Because `b - a ≤ 2α`, the dissipation coefficient is
nonnegative, so the Rusanov flux is entropy stable.

## Frozen decisions

1. Certificates are separate predicates on `(v, ψ, flux)`, as the consistency, monotone and Lipschitz certificates.
   `v` and `ψ` are arbitrary real functions; no differentiability and no relation `ψ = v f - q` is assumed by the
   generic theorems.
2. Results are for the first-order operator `rhs` of B0 on any periodic grid. MUSCL is not covered.
3. Semidiscrete and algebraic only. No fully discrete entropy inequality for Forward Euler or SSP steps.
4. B0--B3 sources do not change.

## Frozen Lean statements

```lean
-- B4-C  (namespace CFDLean.Scalar)
def EntropyStable (v ψ : ℝ → ℝ) (nf : NumericalFlux) : Prop :=
  ∀ a b, (v b - v a) * nf.eval a b ≤ ψ b - ψ a
def EntropyConservative (v ψ : ℝ → ℝ) (nf : NumericalFlux) : Prop :=
  ∀ a b, (v b - v a) * nf.eval a b = ψ b - ψ a
theorem EntropyConservative.entropyStable (h : EntropyConservative v ψ nf) : EntropyStable v ψ nf

-- B4-Q  (namespace CFDLean.Scalar.FiniteVolume)
def entropyFlux (g : Grid I) (v ψ : ℝ → ℝ) (nf : NumericalFlux) (u : I → ℝ) (i : I) : ℝ :=
  (v (u i) + v (u (g.next i))) / 2 * interfaceFlux g nf u i - (ψ (u i) + ψ (u (g.next i))) / 2
theorem entropyFlux_constant (g : Grid I) (v ψ : ℝ → ℝ) (law : ConservationLaw) (nf : NumericalFlux)
    (hc : Consistent law nf) (c : ℝ) (i : I) :
    entropyFlux g v ψ nf (fun _ => c) i = v c * law.flux c - ψ c

-- B4-I
theorem cell_entropy_identity (g : Grid I) (dx : ℝ) (v ψ : ℝ → ℝ) (nf : NumericalFlux) (u : I → ℝ) (i : I) :
    v (u i) * rhs g dx nf u i + (entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx =
      (((v (u (g.next i)) - v (u i)) * nf.eval (u i) (u (g.next i)) - (ψ (u (g.next i)) - ψ (u i))) +
        ((v (u i) - v (u (g.prev i))) * nf.eval (u (g.prev i)) (u i) - (ψ (u i) - ψ (u (g.prev i))))) / (2 * dx)
theorem cell_entropy_inequality (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (v ψ : ℝ → ℝ) (nf : NumericalFlux)
    (h : EntropyStable v ψ nf) (u : I → ℝ) (i : I) :
    v (u i) * rhs g dx nf u i ≤ -(entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx
theorem cell_entropy_equality (g : Grid I) (dx : ℝ) (v ψ : ℝ → ℝ) (nf : NumericalFlux)
    (h : EntropyConservative v ψ nf) (u : I → ℝ) (i : I) :
    v (u i) * rhs g dx nf u i = -(entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx

-- B4-G
theorem entropy_production_nonpos [Fintype I] (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (v ψ : ℝ → ℝ)
    (nf : NumericalFlux) (h : EntropyStable v ψ nf) (u : I → ℝ) : ∑ i, v (u i) * rhs g dx nf u i ≤ 0
theorem entropy_production_zero [Fintype I] (g : Grid I) (dx : ℝ) (v ψ : ℝ → ℝ)
    (nf : NumericalFlux) (h : EntropyConservative v ψ nf) (u : I → ℝ) : ∑ i, v (u i) * rhs g dx nf u i = 0

-- B4-B  (namespace CFDLean.Burgers)
def entropyVariable (u : ℝ) : ℝ := u
def entropyFluxFunction (u : ℝ) : ℝ := u ^ 3 / 3
def entropyPotential (u : ℝ) : ℝ := u ^ 3 / 6
theorem entropyPotential_eq (u : ℝ) :
    entropyPotential u = entropyVariable u * physicalFlux u - entropyFluxFunction u
def EntropyConservativeFlux.eval (a b : ℝ) : ℝ := (a ^ 2 + a * b + b ^ 2) / 6
def EntropyConservativeFlux.numericalFlux : NumericalFlux
theorem EntropyConservativeFlux.consistent : Consistent law EntropyConservativeFlux.numericalFlux
theorem EntropyConservativeFlux.entropyConservative :
    EntropyConservative entropyVariable entropyPotential EntropyConservativeFlux.numericalFlux
theorem Rusanov.eval_eq_entropyConservative_sub (a b : ℝ) :
    Rusanov.eval a b = EntropyConservativeFlux.eval a b - (Rusanov.waveSpeed a b / 2 - (b - a) / 12) * (b - a)
theorem Rusanov.entropyStable : EntropyStable entropyVariable entropyPotential Rusanov.numericalFlux

-- B4-S  (namespace CFDLean.Burgers.Rusanov): instances of B4-I and B4-G for the Rusanov flux on any periodic grid
theorem cell_entropy_inequality (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (u : I → ℝ) (i : I) :
    u i * FiniteVolume.rhs g dx numericalFlux u i ≤
      -(FiniteVolume.entropyFlux g entropyVariable entropyPotential numericalFlux u i -
        FiniteVolume.entropyFlux g entropyVariable entropyPotential numericalFlux u (g.prev i)) / dx
theorem energy_production_nonpos [Fintype I] (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (u : I → ℝ) :
    ∑ i, u i * FiniteVolume.rhs g dx numericalFlux u i ≤ 0
```

## Frozen module layout

```text
CFDLean/Entropy/Scalar/Certificates.lean           B4-C
CFDLean/Entropy/Scalar/Periodic.lean               B4-Q, B4-I, B4-G
CFDLean/Entropy/Scalar/Burgers.lean                B4-B, B4-S
CFDLean/Entropy/Scalar/Controls.lean               exact small controls
CFDLean/Verification/BurgersB4Challenge.lean       trusted statements, Mathlib only
CFDLean/Verification/BurgersB4Verify.lean          bridge
Challenges/BurgersB4.lean                          `lake comparator` challenge
```

## Trusted statements

`CFDLean/Verification/BurgersB4Challenge.lean` imports only Mathlib and restates its own definitions. It states:

| Trusted statement | Content | Result ID |
| --- | --- | --- |
| `EntropyConservativeFluxProperties` | `F_EC(u, u) = u²/2` and `(b - a) F_EC(a, b) = b³/6 - a³/6` | B4-B |
| `RusanovEntropyStable` | `(b - a) F_Rusanov(a, b) ≤ b³/6 - a³/6` | B4-B |
| `CellEntropyInequality I` | for every `next`, `v`, `ψ`, flux with the entropy-stability inequality, `dx > 0`, state and cell: `v_i L_i ≤ -(Q_i - Q_{i-1})/dx` | B4-I |
| `EntropyProductionNonpos I` | the sum over the cells is nonpositive | B4-G |
| `RusanovEnergyProduction I` | `Σ_i u_i L_i(u) ≤ 0` for the Rusanov operator, `dx > 0` | B4-S |

## Relation to the entropy layer of the MC-N core

`CFDLean.Num.antisymmetric_pairFlux` (`CFDLean/Entropy/PairFlux.lean`) gives the production identity for antisymmetric
pair fluxes on a general node set with vector states. The periodic scalar operator is an instance. B4 proves its
statements directly by periodic reindexing; an adapter to the pair-flux form is not part of B4.

## Explicitly excluded from B4

B4 does **not** claim or implement:

- a fully discrete entropy inequality (Forward Euler or SSP steps), an entropy inequality for MUSCL;
- all convex entropies or Kruzhkov entropies (only the certificate form, and the square entropy for Burgers);
- convergence to the entropy solution; uniqueness;
- time derivatives or ODE solutions (`v_i L_i` is not related to `d/dt η(u_i)` in Lean);
- floating-point, arrays, parallel execution.

## Frozen B4 result IDs

| ID | Required result |
| --- | --- |
| B4-C | Entropy-stability and entropy-conservation certificates of a two-point flux |
| B4-Q | Numerical entropy flux and its consistency |
| B4-I | Cell entropy identity; cell entropy inequality (stable flux); cell entropy equality (conservative flux) |
| B4-G | Total entropy production on a periodic grid: nonpositive (stable flux), zero (conservative flux) |
| B4-B | Burgers square-entropy pair; entropy-conservative flux; Rusanov is that flux minus a nonnegative dissipation, so it is entropy stable |
| B4-S | Cell entropy inequality and nonpositive energy production for the Burgers Rusanov operator |

Independent implementation review remains separate from implementation authorization.
