# Burgers B2: SSP Runge-Kutta composition and multi-step stability

Status: **frozen for implementation on 2026-11-26 by the agent under the standing authorization**
(`specifications/Burgers-B2-approval.md`). No human approved the statements of this contract.

Base: Burgers B0 and B1 on `main` at 50299ae. Toolchain: Lean v4.36.0. Exact real arithmetic. No new dependency.

## Purpose

B1 is a one-step result with a CFL hypothesis on the old state. B2 adds

1. generic strong-stability-preserving (SSP) composition: a Runge-Kutta step that is a convex combination of
   Forward-Euler steps inherits every convex invariant set and every convex bound of the Forward-Euler step;
2. generic iteration: a one-step map that keeps a set and does not increase a functional on it does so for every
   number of steps;
3. the Burgers instance: with one time step chosen from the bounds of the initial state, the Rusanov scheme with
   Forward Euler, SSPRK2 or SSPRK3 keeps the bounds and does not increase the total variation, for every number of
   steps.

The generic parts do not mention Burgers, a flux or a grid. They consume a one-step map `E : V → V` on a real vector
space.

## Frozen decisions

1. **SSP methods in Shu-Osher form.** With `E` the Forward-Euler map:
   `ssprk2 E u = ½ u + ½ E(E u)` and `ssprk3 E u = ⅓ u + ⅔ E(¾ u + ¼ E(E u))`.
2. **Mathlib convexity.** Invariant sets use `Convex ℝ S`; functionals use `ConvexOn ℝ S Φ`. No project copy.
3. **State bounds give the CFL condition.** The Burgers hypothesis is `2 · dt · max(|m|, |M|) ≤ dx` for bounds
   `m ≤ u ≤ M` of the initial state. `dt` and `dx` are the same in every step and stage.
4. **Any periodic grid.** The Burgers results are for every `CFDLean.Periodic.Grid I`. The `ZMod N` scheme of B0 is the
   instance `grid`; one lemma states that its step is the general Forward-Euler map.
5. **B0 and B1 sources do not change.**

## Frozen Lean statements

```lean
-- B2-R  (namespace CFDLean.Time.SSP;  V : Type*, [AddCommGroup V] [Module ℝ V])
def ssprk2 (E : V → V) (u : V) : V := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • E (E u)

def ssprk3 (E : V → V) (u : V) : V :=
  (1 / 3 : ℝ) • u + (2 / 3 : ℝ) • E ((3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u))

/-- SSPRK2 of a Forward-Euler map is Heun's method. -/
theorem ssprk2_forwardEuler {I : Type*} (dt : ℝ) (L : (I → ℝ) → I → ℝ) (u : I → ℝ) (i : I) :
    ssprk2 (ForwardEuler.step dt L) u i = u i + dt / 2 * (L u i + L (ForwardEuler.step dt L u) i)

-- B2-C
theorem ssprk2_mem (E : V → V) (S : Set V) (hS : Convex ℝ S) (hE : ∀ u ∈ S, E u ∈ S) (u : V) (hu : u ∈ S) :
    ssprk2 E u ∈ S
theorem ssprk3_mem (E : V → V) (S : Set V) (hS : Convex ℝ S) (hE : ∀ u ∈ S, E u ∈ S) (u : V) (hu : u ∈ S) :
    ssprk3 E u ∈ S
theorem ssprk2_le (E : V → V) (S : Set V) (Φ : V → ℝ) (hΦ : ConvexOn ℝ S Φ) (hE : ∀ u ∈ S, E u ∈ S)
    (hΦE : ∀ u ∈ S, Φ (E u) ≤ Φ u) (u : V) (hu : u ∈ S) : Φ (ssprk2 E u) ≤ Φ u
theorem ssprk3_le (E : V → V) (S : Set V) (Φ : V → ℝ) (hΦ : ConvexOn ℝ S Φ) (hE : ∀ u ∈ S, E u ∈ S)
    (hΦE : ∀ u ∈ S, Φ (E u) ≤ Φ u) (u : V) (hu : u ∈ S) : Φ (ssprk3 E u) ≤ Φ u

-- B2-N  (V : Type*, no structure)
theorem iterate_mem (T : V → V) (S : Set V) (hT : ∀ u ∈ S, T u ∈ S) (u : V) (hu : u ∈ S) (n : ℕ) :
    T^[n] u ∈ S
theorem iterate_le (T : V → V) (S : Set V) (Φ : V → ℝ) (hT : ∀ u ∈ S, T u ∈ S)
    (hΦT : ∀ u ∈ S, Φ (T u) ≤ Φ u) (u : V) (hu : u ∈ S) (n : ℕ) : Φ (T^[n] u) ≤ Φ u

-- B2-L
theorem ssprk2_fixed (E : V → V) (c : V) (hc : E c = c) : ssprk2 E c = c
theorem ssprk3_fixed (E : V → V) (c : V) (hc : E c = c) : ssprk3 E c = c
theorem ssprk2_linear (E : V → V) (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ∀ u, ℓ (E u) = ℓ u) (u : V) : ℓ (ssprk2 E u) = ℓ u
theorem ssprk3_linear (E : V → V) (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ∀ u, ℓ (E u) = ℓ u) (u : V) : ℓ (ssprk3 E u) = ℓ u

-- B2-B  (namespace CFDLean.Scalar.FiniteVolume, then CFDLean.Burgers.Rusanov)
def boundedStates (m M : ℝ) : Set (I → ℝ) := {u | ∀ j, m ≤ u j ∧ u j ≤ M}

theorem boundedStates_convex (m M : ℝ) : Convex ℝ (boundedStates (I := I) m M)
theorem totalVariation_convexOn [Fintype I] (g : Grid I) (S : Set (I → ℝ)) (hS : Convex ℝ S) :
    ConvexOn ℝ S (totalVariation g)

/-- The Rusanov Forward-Euler map of B0 on a grid. -/
def eulerStep (g : Grid I) (dx dt : ℝ) : (I → ℝ) → I → ℝ :=
  Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux)

theorem waveSpeed_le_of_bounds (m M a b : ℝ) (ha : m ≤ a ∧ a ≤ M) (hb : m ≤ b ∧ b ≤ M) :
    waveSpeed a b ≤ max |m| |M|
theorem eulerStep_mem (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ FiniteVolume.boundedStates m M) :
    eulerStep g dx dt u ∈ FiniteVolume.boundedStates m M
theorem eulerStep_totalVariation_le [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ FiniteVolume.boundedStates m M) :
    FiniteVolume.totalVariation g (eulerStep g dx dt u) ≤ FiniteVolume.totalVariation g u

-- B2-S  (namespace CFDLean.Burgers.Rusanov)
def ssprk2Step (g : Grid I) (dx dt : ℝ) : (I → ℝ) → I → ℝ := Time.SSP.ssprk2 (eulerStep g dx dt)
def ssprk3Step (g : Grid I) (dx dt : ℝ) : (I → ℝ) → I → ℝ := Time.SSP.ssprk3 (eulerStep g dx dt)

-- one theorem for each T in {eulerStep, ssprk2Step, ssprk3Step}:
theorem T_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ FiniteVolume.boundedStates m M) (n : ℕ) :
    (T g dx dt)^[n] u ∈ FiniteVolume.boundedStates m M ∧
      FiniteVolume.totalVariation g ((T g dx dt)^[n] u) ≤ FiniteVolume.totalVariation g u

-- one theorem for each T in {ssprk2Step, ssprk3Step}:
theorem T_sum [Fintype I] (g : Grid I) (dx dt : ℝ) (hdx : dx ≠ 0) (u : I → ℝ) :
    ∑ i, T g dx dt u i = ∑ i, u i
theorem T_constant (g : Grid I) (dx dt c : ℝ) : T g dx dt (fun _ => c) = fun _ => c
```

Supporting lemmas may be added with any name.

## Frozen module layout

```text
CFDLean/Time/SSP.lean                              B2-R, B2-C, B2-N, B2-L
CFDLean/Discrete/Periodic/Convexity.lean           B2-B generic part (boundedStates, convexity)
CFDLean/Schemes/Burgers/RusanovSSP.lean            B2-B Rusanov part, B2-S
CFDLean/Schemes/Burgers/SSPControls.lean           exact small controls
CFDLean/Verification/BurgersB2Challenge.lean       trusted statements, Mathlib only
CFDLean/Verification/BurgersB2Verify.lean          bridge
Challenges/BurgersB2.lean                          `lake comparator` challenge
```

## Trusted statements

`CFDLean/Verification/BurgersB2Challenge.lean` imports only Mathlib and restates its own definitions (Rusanov flux,
periodic step on `next : I ≃ I`, total variation, `ssprk2`, `ssprk3`). It states:

| Trusted statement | Content | Result ID |
| --- | --- | --- |
| `SSPRK2Convex V`, `SSPRK3Convex V` | for every `E`, convex `S` kept by `E` and `Φ` convex on `S` not increased by `E`: the SSP step keeps `S` and does not increase `Φ` | B2-C |
| `EulerMultiStep I` | bounds and total variation after `n` Forward-Euler steps | B2-S |
| `SSPRK2MultiStep I`, `SSPRK3MultiStep I` | the same for `n` SSPRK2 or SSPRK3 steps | B2-S |
| `SSPRK2Conservation I`, `SSPRK3Conservation I` | one SSP step keeps the total sum when `dx ≠ 0` | B2-S |

The multi-step statements have the hypotheses `0 < dx`, `0 ≤ dt`, `2 · dt · max(|m|, |M|) ≤ dx` and
`m ≤ u_j ≤ M` for the initial state, and hold for every `n`.

## Explicitly excluded from B2

B2 does **not** claim or implement:

- order of accuracy of SSPRK2 or SSPRK3 (no Taylor expansion, no consistency order);
- optimality of the SSP coefficient, other Runge-Kutta or multistep methods;
- a time step that changes between steps, a CFL estimator;
- entropy inequalities, convergence;
- reconstruction and limiters (B3), floating-point, arrays, parallel execution.

## Frozen B2 result IDs

| ID | Required result |
| --- | --- |
| B2-R | SSPRK2 and SSPRK3 in Shu-Osher form over a one-step map; SSPRK2 of Forward Euler is Heun's method |
| B2-C | Generic SSP composition: convex invariant sets and convex bounds pass from the Euler map to the SSP step |
| B2-N | Generic iteration of an invariant set and of a non-increasing functional |
| B2-L | Generic fixed points and linear invariants of the SSP steps |
| B2-B | Bounded states are convex; total variation is convex; the Rusanov Euler map keeps bounds and is TVD on bounded states |
| B2-S | Multi-step bounds and TVD for Euler, SSPRK2, SSPRK3 with Rusanov; conservation and constant states for the SSP steps |

Independent implementation review remains separate from implementation authorization.
