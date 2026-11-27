import CFDLean.Schemes.Burgers.Nonuniform

/-! Checks for the Burgers instance of FVN (task 4): FVN-U(b), FVN-B and FVN-MB applied to their own hypotheses, the
one-cell grid on a concrete mesh (review focus 1), the degenerate interval `hi ≤ lo` (review focus 3) and the
`θ = 2` limiters on a uniform mesh. -/
noncomputable section
namespace CFDLean.Burgers.Nonuniform.Checks

open CFDLean.Periodic
open CFDLean.Scalar.FiniteVolume (SlopeBounded boundedStates totalVariation limitedSlope mcFactor
  slopeBounded_mcFactor)

variable {I : Type*}

/-! ### Definitions -/

example : face = FV1D.face physicalFlux Rusanov.waveSpeed := rfl

example : face = Rusanov.numericalFlux.eval := face_eq

example (m : Mesh1D I) (dt : ℝ) : firstOrderStep m dt = FV1D.Nonuniform.firstOrderStep m face dt := rfl

example (m : Mesh1D I) (dt : ℝ) (φ : ℝ → ℝ → ℝ) :
    musclStep m dt φ = FV1D.Nonuniform.musclStep m face φ dt := rfl

example (m : Mesh1D I) (dt : ℝ) (φ : ℝ → ℝ → ℝ) :
    musclSsprk2Step m dt φ = Time.SSP.ssprk2 (musclStep m dt φ) := rfl

example (m : Mesh1D I) (dt : ℝ) (φ : ℝ → ℝ → ℝ) :
    musclSsprk3Step m dt φ = Time.SSP.ssprk3 (musclStep m dt φ) := rfl

/-! ### FVN-U(b) -/

example (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (dt : ℝ) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) :
    musclStep (Mesh1D.uniform g dx hdx) dt φ u i = Rusanov.musclEulerStep g dx dt φ u i :=
  musclStep_uniform g dx hdx dt φ u i

/-! ### FVN-B -/

example (m : Mesh1D I) (dt : ℝ) (hdt : 0 ≤ dt) (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi)
    (hcfl : ∀ i, dt * (Rusanov.waveSpeed (u (m.grid.prev i)) (u (m.grid.next (m.grid.prev i))) +
      Rusanov.waveSpeed (u i) (u (m.grid.next i))) ≤ m.width i) :
    firstOrderStep m dt u ∈ boundedStates lo hi :=
  firstOrderStep_mem m dt hdt lo hi u hu hcfl

example [Fintype I] (m : Mesh1D I) (dt : ℝ) (hdt : 0 ≤ dt) (u : I → ℝ)
    (hcfl : ∀ i, dt * Rusanov.waveSpeed (u i) (u (m.grid.next i)) ≤ min (m.width i) (m.width (m.grid.next i))) :
    totalVariation m.grid (firstOrderStep m dt u) ≤ totalVariation m.grid u :=
  firstOrderStep_totalVariation_le m dt hdt u hcfl

/-- Review focus 3: FVN-B (a) on a degenerate interval `hi ≤ lo`; no `lo < hi` premise. -/
example (m : Mesh1D I) (dt : ℝ) (hdt : 0 ≤ dt) (c : ℝ)
    (hcfl : ∀ i, dt * (Rusanov.waveSpeed c c + Rusanov.waveSpeed c c) ≤ m.width i) :
    firstOrderStep m dt (fun _ => c) ∈ boundedStates c c :=
  firstOrderStep_mem m dt hdt c c _ (fun _ => ⟨le_rfl, le_rfl⟩) hcfl

/-! ### FVN-MB -/

example [Fintype I] (m : Mesh1D I) (dt lo hi : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ m.width i) (u : I → ℝ)
    (hu : u ∈ boundedStates lo hi) (n : ℕ) :
    (musclStep m dt φ)^[n] u ∈ boundedStates lo hi ∧
      totalVariation m.grid ((musclStep m dt φ)^[n] u) ≤ totalVariation m.grid u :=
  musclStep_iterate_stable m dt lo hi φ θ hφ hr hdt hcfl u hu n

example [Fintype I] (m : Mesh1D I) (dt lo hi : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ m.width i) (u : I → ℝ)
    (hu : u ∈ boundedStates lo hi) (n : ℕ) :
    (musclSsprk2Step m dt φ)^[n] u ∈ boundedStates lo hi ∧
      totalVariation m.grid ((musclSsprk2Step m dt φ)^[n] u) ≤ totalVariation m.grid u :=
  musclSsprk2Step_iterate_stable m dt lo hi φ θ hφ hr hdt hcfl u hu n

example [Fintype I] (m : Mesh1D I) (dt lo hi : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ m.width i) (u : I → ℝ)
    (hu : u ∈ boundedStates lo hi) (n : ℕ) :
    (musclSsprk3Step m dt φ)^[n] u ∈ boundedStates lo hi ∧
      totalVariation m.grid ((musclSsprk3Step m dt φ)^[n] u) ≤ totalVariation m.grid u :=
  musclSsprk3Step_iterate_stable m dt lo hi φ θ hφ hr hdt hcfl u hu n

/-- The contract's one SSPRK3 step is the case `n = 1`. -/
example [Fintype I] (m : Mesh1D I) (dt lo hi : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ m.width i) (u : I → ℝ)
    (hu : u ∈ boundedStates lo hi) :
    musclSsprk3Step m dt φ u ∈ boundedStates lo hi ∧
      totalVariation m.grid (musclSsprk3Step m dt φ u) ≤ totalVariation m.grid u :=
  musclSsprk3Step_iterate_stable m dt lo hi φ θ hφ hr hdt hcfl u hu 1

/-- Review focus 3: FVN-MB on a degenerate interval `hi ≤ lo`; no `lo < hi` premise. -/
example [Fintype I] (m : Mesh1D I) (dt : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (c : ℝ) (hcfl : ∀ i, 8 * dt * max |c| |c| ≤ m.width i) (n : ℕ) :
    (musclSsprk3Step m dt φ)^[n] (fun _ => c) ∈ boundedStates c c :=
  (musclSsprk3Step_iterate_stable m dt c c φ θ hφ hr hdt hcfl _ (fun _ => ⟨le_rfl, le_rfl⟩) n).1

/-- The uniform mesh has mesh ratio `2`, so FVN-MB covers the MC limiter (`θ = 2`) there. -/
example [Fintype I] (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (dt lo hi : ℝ) (hdt : 0 ≤ dt)
    (hcfl : 8 * dt * max |lo| |hi| ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (n : ℕ) :
    (musclSsprk3Step (Mesh1D.uniform g dx hdx) dt (limitedSlope mcFactor))^[n] u ∈ boundedStates lo hi ∧
      totalVariation g ((musclSsprk3Step (Mesh1D.uniform g dx hdx) dt (limitedSlope mcFactor))^[n] u) ≤
        totalVariation g u :=
  musclSsprk3Step_iterate_stable (Mesh1D.uniform g dx hdx) dt lo hi _ 2 slopeBounded_mcFactor
    (fun _ => by simp only [Mesh1D.uniform, max_self]; linarith) hdt (fun _ => hcfl) u hu n

/-! ### Review focus 1: one cell

On `ZMod 1` the face from the only cell leads back to it, so `next i = prev i = i` and both faces of the cell carry
the same flux. The concrete mesh below has one cell of width `1`. -/

/-- The one-cell mesh of width `1` (a local notation, not a declaration). -/
local notation "oneCell" => Mesh1D.uniform (zmodGrid 1) 1 one_pos

/-- FVN-B (a) on the one-cell mesh, applied to its own hypotheses. -/
example (dt : ℝ) (hdt : 0 ≤ dt) (lo hi : ℝ) (u : ZMod 1 → ℝ) (hu : u ∈ boundedStates lo hi)
    (hcfl : ∀ i, dt * (Rusanov.waveSpeed (u ((oneCell).grid.prev i)) (u ((oneCell).grid.next ((oneCell).grid.prev i))) +
      Rusanov.waveSpeed (u i) (u ((oneCell).grid.next i))) ≤ (oneCell).width i) :
    firstOrderStep oneCell dt u ∈ boundedStates lo hi :=
  firstOrderStep_mem oneCell dt hdt lo hi u hu hcfl

/-- FVN-B (b) on the one-cell mesh, applied to its own hypotheses. -/
example (dt : ℝ) (hdt : 0 ≤ dt) (u : ZMod 1 → ℝ)
    (hcfl : ∀ i, dt * Rusanov.waveSpeed (u i) (u ((oneCell).grid.next i)) ≤
      min ((oneCell).width i) ((oneCell).width ((oneCell).grid.next i))) :
    totalVariation (oneCell).grid (firstOrderStep oneCell dt u) ≤ totalVariation (oneCell).grid u :=
  firstOrderStep_totalVariation_le oneCell dt hdt u hcfl

/-- One cell, closed: the state `1/2` in `[0, 1]` with `dt = 1`. Both CFL conditions hold, the bound CFL with
equality: `1 · (1/2 + 1/2) = 1`. -/
example : firstOrderStep oneCell 1 (fun _ => 1 / 2) ∈ boundedStates 0 1 :=
  firstOrderStep_mem oneCell 1 zero_le_one 0 1 _ (fun _ => by norm_num) fun _ => by
    norm_num [Rusanov.waveSpeed, Mesh1D.uniform]

/-- One cell, closed: total variation with `dt = 1`, where `1 · 1/2 ≤ min 1 1`. -/
example : totalVariation (oneCell).grid (firstOrderStep oneCell 1 (fun _ => 1 / 2)) ≤
    totalVariation (oneCell).grid (fun _ => (1 / 2 : ℝ)) :=
  firstOrderStep_totalVariation_le oneCell 1 zero_le_one _ fun _ => by
    norm_num [Rusanov.waveSpeed, Mesh1D.uniform]

/-- FVN-MB on the one-cell mesh with the MC limiter (`θ = 2`), applied to its own hypotheses. -/
example (dt lo hi : ℝ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ (oneCell).width i)
    (u : ZMod 1 → ℝ) (hu : u ∈ boundedStates lo hi) (n : ℕ) :
    (musclSsprk3Step oneCell dt (limitedSlope mcFactor))^[n] u ∈ boundedStates lo hi ∧
      totalVariation (oneCell).grid ((musclSsprk3Step oneCell dt (limitedSlope mcFactor))^[n] u) ≤
        totalVariation (oneCell).grid u :=
  musclSsprk3Step_iterate_stable oneCell dt lo hi _ 2 slopeBounded_mcFactor
    (fun _ => by norm_num [Mesh1D.uniform]) hdt hcfl u hu n

/-- FVN-U(b) on the one-cell mesh. -/
example (dt : ℝ) (φ : ℝ → ℝ → ℝ) (u : ZMod 1 → ℝ) (i : ZMod 1) :
    musclStep oneCell dt φ u i = Rusanov.musclEulerStep (zmodGrid 1) 1 dt φ u i :=
  musclStep_uniform (zmodGrid 1) 1 one_pos dt φ u i

end CFDLean.Burgers.Nonuniform.Checks
