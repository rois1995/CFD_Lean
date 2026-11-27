import CFDLean.Discrete.Periodic.NonuniformMusclStability

/-! Checks for the FVN layers on a non-uniform periodic 1D mesh, in three sections:

- the reconstruction-independent layer (task 1): the flux-form update and the first-order step, FVN-C, FVN-K and
  FVN-U(a);
- the MUSCL realization (task 2): the rescaled differences, slope and face states as frozen, FVN-C and FVN-K for the
  MUSCL step, and FVN-A;
- the scalar MUSCL stability (task 3): FVN-R, FVN-M and the incremental form, including the degenerate interval
  `[c, c]` (review focus 3).

Each section applies every public theorem to its own hypotheses and adds instances on the one-cell grid `ZMod 1`
(where `next i = prev i = i`, review focus 1); the first two also check the step with `dt = 0` (review focus 2). -/
noncomputable section
namespace CFDLean.FV1D.Nonuniform.Checks

open Periodic
open scoped BigOperators

variable {S I : Type*} [AddCommGroup S] [Module ℝ S]

/-! ### Reconstruction-independent layer (task 1) -/

example [Fintype I] (m : Mesh1D I) (dt : ℝ) (h U : I → S) :
    ∑ i, m.width i • update m dt h U i = ∑ i, m.width i • U i :=
  update_weighted_sum m dt h U

example [Fintype I] (m : Mesh1D I) (H : S → S → S) (dt : ℝ) (U : I → S) :
    ∑ i, m.width i • firstOrderStep m H dt U i = ∑ i, m.width i • U i :=
  firstOrderStep_weighted_sum m H dt U

example (m : Mesh1D I) (H : S → S → S) (dt : ℝ) (C : S) :
    firstOrderStep m H dt (fun _ => C) = fun _ => C :=
  firstOrderStep_constant m H dt C

example (g : Grid I) (F : S → S) (a : S → S → ℝ) (dx : ℝ) (hdx : 0 < dx) (dt : ℝ) (U : I → S) (i : I) :
    firstOrderStep (Mesh1D.uniform g dx hdx) (FV1D.face F a) dt U i = FV1D.step g F a dx dt U i :=
  firstOrderStep_uniform g F a dx hdx dt U i

/-- Review focus 1: the one-cell grid needs no extra hypothesis for FVN-C. -/
example (m : Mesh1D (ZMod 1)) (H : S → S → S) (dt : ℝ) (U : ZMod 1 → S) :
    ∑ i, m.width i • firstOrderStep m H dt U i = ∑ i, m.width i • U i :=
  firstOrderStep_weighted_sum m H dt U

/-- Review focus 1: the one-cell grid needs no extra hypothesis for FVN-K. -/
example (m : Mesh1D (ZMod 1)) (H : S → S → S) (dt : ℝ) (C : S) :
    firstOrderStep m H dt (fun _ => C) = fun _ => C :=
  firstOrderStep_constant m H dt C

/-- Review focus 2: with `dt = 0` the first-order step returns its input. -/
example (m : Mesh1D I) (H : S → S → S) (U : I → S) : firstOrderStep m H 0 U = U := by
  funext i
  simp [firstOrderStep, update]

/-! ### MUSCL realization (task 2)

The rescaled differences and face states as frozen, each public theorem applied to its own hypotheses, the one-cell
grid and the step with `dt = 0`. -/

/-- The backward difference is rescaled by the cell's own width over the spacing of its left face. -/
example (m : Mesh1D I) (U : I → S) (i : I) :
    backDiff m U i = (m.width i / m.spacing (m.grid.prev i)) • (U i - U (m.grid.prev i)) :=
  rfl

/-- The forward difference is rescaled by the cell's own width over the spacing of its right face. -/
example (m : Mesh1D I) (U : I → S) (i : I) :
    fwdDiff m U i = (m.width i / m.spacing i) • (U (m.grid.next i) - U i) :=
  rfl

example (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) :
    slope m lim U i = lim (backDiff m U i) (fwdDiff m U i) :=
  rfl

example (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) :
    leftState m lim U i = U i + (1 / 2 : ℝ) • slope m lim U i :=
  rfl

example (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) :
    rightState m lim U i = U (m.grid.next i) - (1 / 2 : ℝ) • slope m lim U (m.grid.next i) :=
  rfl

/-- The MUSCL step is the generic update fed with the MUSCL face fluxes. -/
example (m : Mesh1D I) (H lim : S → S → S) (dt : ℝ) (U : I → S) :
    musclStep m H lim dt U = update m dt (fun j => H (leftState m lim U j) (rightState m lim U j)) U :=
  rfl

example {n : ℕ} (φ : ℝ → ℝ → ℝ) (A B : Fin n → ℝ) (k : Fin n) :
    componentwise φ A B k = φ (A k) (B k) :=
  rfl

example [Fintype I] (m : Mesh1D I) (H lim : S → S → S) (dt : ℝ) (U : I → S) :
    ∑ i, m.width i • musclStep m H lim dt U i = ∑ i, m.width i • U i :=
  musclStep_weighted_sum m H lim dt U

example (m : Mesh1D I) (H lim : S → S → S) (dt : ℝ) (C : S) (hlim : lim 0 0 = 0) :
    musclStep m H lim dt (fun _ => C) = fun _ => C :=
  musclStep_constant m H lim dt C hlim

example (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) (β : S) (hlim : ∀ d, lim d d = d)
    (hf : U (m.grid.next i) - U i = m.spacing i • β)
    (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) :
    leftState m lim U i = U i + (m.width i / 2) • β :=
  leftState_affine m lim U i β hlim hf hb

example (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) (β : S) (hlim : ∀ d, lim d d = d)
    (hf : U (m.grid.next i) - U i = m.spacing i • β)
    (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) :
    rightState m lim U (m.grid.prev i) = U i - (m.width i / 2) • β :=
  rightState_prev_affine m lim U i β hlim hf hb

/-- Review focus 1: the one-cell grid needs no extra hypothesis for the MUSCL part of FVN-C. -/
example (m : Mesh1D (ZMod 1)) (H lim : S → S → S) (dt : ℝ) (U : ZMod 1 → S) :
    ∑ i, m.width i • musclStep m H lim dt U i = ∑ i, m.width i • U i :=
  musclStep_weighted_sum m H lim dt U

/-- Review focus 1: the one-cell grid needs no extra hypothesis for the MUSCL part of FVN-K. -/
example (m : Mesh1D (ZMod 1)) (H lim : S → S → S) (dt : ℝ) (C : S) (hlim : lim 0 0 = 0) :
    musclStep m H lim dt (fun _ => C) = fun _ => C :=
  musclStep_constant m H lim dt C hlim

/-- Review focus 1: FVN-A on the one-cell grid, where both differences vanish and `β` is forced to `0`. -/
example (m : Mesh1D (ZMod 1)) (lim : S → S → S) (U : ZMod 1 → S) (i : ZMod 1) (β : S)
    (hlim : ∀ d, lim d d = d)
    (hf : U (m.grid.next i) - U i = m.spacing i • β)
    (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) :
    leftState m lim U i = U i + (m.width i / 2) • β :=
  leftState_affine m lim U i β hlim hf hb

/-- Review focus 1: FVN-A for the right state on the one-cell grid, where `prev i = i`. -/
example (m : Mesh1D (ZMod 1)) (lim : S → S → S) (U : ZMod 1 → S) (i : ZMod 1) (β : S)
    (hlim : ∀ d, lim d d = d)
    (hf : U (m.grid.next i) - U i = m.spacing i • β)
    (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) :
    rightState m lim U (m.grid.prev i) = U i - (m.width i / 2) • β :=
  rightState_prev_affine m lim U i β hlim hf hb

/-- Review focus 2: with `dt = 0` the MUSCL step returns its input. -/
example (m : Mesh1D I) (H lim : S → S → S) (U : I → S) : musclStep m H lim 0 U = U := by
  funext i
  simp [musclStep, update]

/-! ### Scalar MUSCL stability (task 3)

FVN-R and FVN-M applied to their own hypotheses, the incremental form, the degenerate interval `[c, c]` (review
focus 3) and the one-cell grid. -/

section Stability

open CFDLean.Scalar (NumericalFlux MonotoneFlux LipschitzOnBounds)
open CFDLean.Scalar.FiniteVolume (SlopeBounded boundedStates totalVariation incrementalUpdate)

example (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ) (lo hi : ℝ)
    (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (i : I) :
    lo ≤ leftState m φ u i ∧ leftState m φ u i ≤ hi :=
  leftState_mem m φ θ hφ hr lo hi u hu i

example (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ) (lo hi : ℝ)
    (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (i : I) :
    lo ≤ rightState m φ u i ∧ rightState m φ u i ≤ hi :=
  rightState_mem m φ θ hφ hr lo hi u hu i

example (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ) (lo hi : ℝ)
    (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (nf : NumericalFlux) (hmono : MonotoneFlux nf) (KL KR : ℝ)
    (hlip : LipschitzOnBounds nf lo hi KL KR) (dt : ℝ) (hdt : 0 ≤ dt)
    (hcfl : ∀ i, dt * ((KL + KR) / m.width i + θ * (KR / (m.width i + m.width (m.grid.next i)) +
      KL / (m.width (m.grid.prev i) + m.width i))) ≤ 1) :
    musclStep m nf.eval φ dt u ∈ boundedStates lo hi :=
  musclStep_mem m φ θ hφ hr lo hi u hu nf hmono KL KR hlip dt hdt hcfl

example [Fintype I] (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ)
    (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (nf : NumericalFlux) (hmono : MonotoneFlux nf)
    (KL KR : ℝ) (hlip : LipschitzOnBounds nf lo hi KL KR) (dt : ℝ) (hdt : 0 ≤ dt)
    (hcfl : ∀ i, dt * (KR / m.width i + KL / m.width (m.grid.next i) +
      θ * (KL + KR) / (m.width i + m.width (m.grid.next i))) ≤ 1) :
    totalVariation m.grid (musclStep m nf.eval φ dt u) ≤ totalVariation m.grid u :=
  musclStep_totalVariation_le m φ θ hφ hr lo hi u hu nf hmono KL KR hlip dt hdt hcfl

/-- The incremental form with the coefficient bounds `(dt/w i) KR (1 + θ p i)` and
`(dt/w (next i)) KL (1 + θ q i)`. -/
example (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ) (lo hi : ℝ)
    (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (nf : NumericalFlux) (hmono : MonotoneFlux nf) (KL KR : ℝ)
    (hlip : LipschitzOnBounds nf lo hi KL KR) (hKL : 0 ≤ KL) (hKR : 0 ≤ KR) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∃ C D : I → ℝ,
      (∀ i, 0 ≤ C i ∧
        C i ≤ dt / m.width i * KR * (1 + θ * (m.width i / (m.width i + m.width (m.grid.next i))))) ∧
      (∀ i, 0 ≤ D i ∧ D i ≤ dt / m.width (m.grid.next i) * KL *
        (1 + θ * (m.width (m.grid.next i) / (m.width i + m.width (m.grid.next i))))) ∧
      musclStep m nf.eval φ dt u = incrementalUpdate m.grid C D u :=
  musclStep_incremental m φ θ hφ hr lo hi u hu nf hmono KL KR hlip hKL hKR dt hdt

/-- Review focus 3, concrete: on the interval `[c, c]` the Lipschitz certificate holds with `KL = KR = -1`, which
no nondegenerate interval allows, and `musclStep_mem` still applies. -/
example (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ)
    (nf : NumericalFlux) (hmono : MonotoneFlux nf) (c dt : ℝ) (hdt : 0 ≤ dt) :
    musclStep m nf.eval φ dt (fun _ => c) ∈ boundedStates c c := by
  refine musclStep_mem m φ θ hφ hr c c _ (fun _ => ⟨le_rfl, le_rfl⟩) nf hmono (-1) (-1)
    ⟨fun a a' _ h1 h2 h3 h4 _ _ => by rw [le_antisymm h2 h1, le_antisymm h4 h3]; simp,
      fun _ b b' _ _ h3 h4 h5 h6 => by rw [le_antisymm h4 h3, le_antisymm h6 h5]; simp⟩ dt hdt fun i => ?_
  have hθ := hφ.nonneg
  have h0 : 0 ≤ (1 + 1) / m.width i + θ * (1 / (m.width i + m.width (m.grid.next i)) +
      1 / (m.width (m.grid.prev i) + m.width i)) := by
    have := m.width_pos i
    have := m.width_pos (m.grid.next i)
    have := m.width_pos (m.grid.prev i)
    positivity
  have e : dt * ((-1 + -1) / m.width i + θ * (-1 / (m.width i + m.width (m.grid.next i)) +
      -1 / (m.width (m.grid.prev i) + m.width i))) = -(dt * ((1 + 1) / m.width i +
      θ * (1 / (m.width i + m.width (m.grid.next i)) + 1 / (m.width (m.grid.prev i) + m.width i)))) := by
    ring
  rw [e]
  linarith [mul_nonneg hdt h0]

/-- Review focus 3, concrete: `musclStep_totalVariation_le` on the interval `[c, c]` with the same certificate
`KL = KR = -1`, under which the CFL premise holds for every `dt ≥ 0`. -/
example [Fintype I] (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ)
    (nf : NumericalFlux) (hmono : MonotoneFlux nf) (c dt : ℝ) (hdt : 0 ≤ dt) :
    totalVariation m.grid (musclStep m nf.eval φ dt (fun _ => c)) ≤ totalVariation m.grid (fun _ => c) := by
  refine musclStep_totalVariation_le m φ θ hφ hr c c _ (fun _ => ⟨le_rfl, le_rfl⟩) nf hmono (-1) (-1)
    ⟨fun a a' _ h1 h2 h3 h4 _ _ => by rw [le_antisymm h2 h1, le_antisymm h4 h3]; simp,
      fun _ b b' _ _ h3 h4 h5 h6 => by rw [le_antisymm h4 h3, le_antisymm h6 h5]; simp⟩ dt hdt fun i => ?_
  have hθ := hφ.nonneg
  have h0 : 0 ≤ 1 / m.width i + 1 / m.width (m.grid.next i) +
      θ * (1 + 1) / (m.width i + m.width (m.grid.next i)) := by
    have := m.width_pos i
    have := m.width_pos (m.grid.next i)
    positivity
  have e : dt * (-1 / m.width i + -1 / m.width (m.grid.next i) +
      θ * (-1 + -1) / (m.width i + m.width (m.grid.next i))) = -(dt * (1 / m.width i +
      1 / m.width (m.grid.next i) + θ * (1 + 1) / (m.width i + m.width (m.grid.next i)))) := by
    ring
  rw [e]
  linarith [mul_nonneg hdt h0]

/-- Review focus 1: FVN-M on the one-cell grid needs no extra hypothesis. -/
example (m : Mesh1D (ZMod 1)) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ)
    (lo hi : ℝ) (u : ZMod 1 → ℝ) (hu : u ∈ boundedStates lo hi) (nf : NumericalFlux) (hmono : MonotoneFlux nf)
    (KL KR : ℝ) (hlip : LipschitzOnBounds nf lo hi KL KR) (dt : ℝ) (hdt : 0 ≤ dt)
    (hcfl : ∀ i, dt * (KR / m.width i + KL / m.width (m.grid.next i) +
      θ * (KL + KR) / (m.width i + m.width (m.grid.next i))) ≤ 1) :
    totalVariation m.grid (musclStep m nf.eval φ dt u) ≤ totalVariation m.grid u :=
  musclStep_totalVariation_le m φ θ hφ hr lo hi u hu nf hmono KL KR hlip dt hdt hcfl

end Stability

end CFDLean.FV1D.Nonuniform.Checks
