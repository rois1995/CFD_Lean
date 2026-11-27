import CFDLean.Discrete.Periodic.NonuniformMusclStability
import CFDLean.Schemes.Burgers.FV1D
import CFDLean.Schemes.Burgers.RusanovLimiters

/-! FVN-U(b), FVN-B and FVN-MB: the Burgers instance of the steps on a non-uniform periodic 1D mesh.

The face flux is the FV1D Rusanov face of the Burgers flux, `face = FV1D.face physicalFlux Rusanov.waveSpeed`, which
is the B0 Rusanov flux `Rusanov.eval` (`fv1d_face_eq`).

- FVN-U(b): on the uniform mesh the rescaling factors are `dx / ((dx + dx) / 2) = 1`, so the MUSCL step is the
  accepted B3 step `Rusanov.musclEulerStep`.
- FVN-B: with `a i = max (|u i|, |u (next i)|)` and `mean i = (u i + u (next i)) / 2`, the first-order step is a
  Harten incremental update with `C i = dt / w i · (a i − mean i) / 2` and
  `D i = dt / w (next i) · (a i + mean i) / 2`. Both are nonnegative because `|mean i| ≤ a i`
  (`abs_mean_le_waveSpeed`), so the cell CFL `dt (a (prev i) + a i) ≤ w i` gives the bounds and the face CFL
  `dt · a i ≤ min (w i) (w (next i))` gives the total variation.
- FVN-MB: FVN-M with the B3 Lipschitz certificate `KL = KR = 2A`, `A = max (|lo|, |hi|)`. The mesh ratio gives
  `θ p i ≤ 1` and `θ q i ≤ 1`, so both FVN-M conditions follow from `8 · dt · A ≤ w i`. The SSPRK2 and SSPRK3
  steps are wired as in `RusanovLimiters`. -/
noncomputable section
namespace CFDLean.Burgers.Nonuniform

open CFDLean.Periodic
open CFDLean.Scalar.FiniteVolume (SlopeBounded boundedStates boundedStates_convex totalVariation
  totalVariation_convexOn incrementalUpdate incrementalUpdate_bounds incrementalUpdate_totalVariation_le)

variable {I : Type*}

/-! ### Definitions -/

/-- The Burgers face flux: the FV1D Rusanov face of the Burgers flux. -/
def face : ℝ → ℝ → ℝ := FV1D.face physicalFlux Rusanov.waveSpeed

/-- First-order Burgers step on a non-uniform mesh. -/
def firstOrderStep (m : Mesh1D I) (dt : ℝ) : (I → ℝ) → I → ℝ :=
  FV1D.Nonuniform.firstOrderStep m face dt

/-- Burgers MUSCL Forward-Euler step on a non-uniform mesh with limiter `φ`. -/
def musclStep (m : Mesh1D I) (dt : ℝ) (φ : ℝ → ℝ → ℝ) : (I → ℝ) → I → ℝ :=
  FV1D.Nonuniform.musclStep m face φ dt

/-- One SSPRK2 step of the Burgers MUSCL scheme on a non-uniform mesh. -/
def musclSsprk2Step (m : Mesh1D I) (dt : ℝ) (φ : ℝ → ℝ → ℝ) : (I → ℝ) → I → ℝ :=
  Time.SSP.ssprk2 (musclStep m dt φ)

/-- One SSPRK3 step of the Burgers MUSCL scheme on a non-uniform mesh. -/
def musclSsprk3Step (m : Mesh1D I) (dt : ℝ) (φ : ℝ → ℝ → ℝ) : (I → ℝ) → I → ℝ :=
  Time.SSP.ssprk3 (musclStep m dt φ)

/-- The Burgers face is the B0 Rusanov flux. -/
theorem face_eq : face = Rusanov.numericalFlux.eval :=
  funext fun L => funext fun R => fv1d_face_eq L R

/-! ### FVN-U(b) -/

/-- On the uniform mesh both rescaling factors are `dx / ((dx + dx) / 2) = 1`. -/
private theorem uniform_factor (dx : ℝ) (hdx : 0 < dx) : dx / ((dx + dx) / 2) = 1 := by
  rw [add_self_div_two, div_self hdx.ne']

/-- On the uniform mesh the rescaled slope is the B3 slope. -/
private theorem slope_uniform (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) :
    FV1D.Nonuniform.slope (Mesh1D.uniform g dx hdx) φ u i = Scalar.FiniteVolume.slope g φ u i := by
  simp only [FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff, Mesh1D.spacing,
    Mesh1D.uniform, uniform_factor dx hdx, one_smul, Scalar.FiniteVolume.slope]

/-- On the uniform mesh the left state is the B3 left state. -/
private theorem leftState_uniform (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) :
    FV1D.Nonuniform.leftState (Mesh1D.uniform g dx hdx) φ u i = Scalar.FiniteVolume.leftState g φ u i := by
  rw [FV1D.Nonuniform.leftState, slope_uniform, Scalar.FiniteVolume.leftState, smul_eq_mul]
  ring

/-- On the uniform mesh the right state is the B3 right state. -/
private theorem rightState_uniform (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) :
    FV1D.Nonuniform.rightState (Mesh1D.uniform g dx hdx) φ u i = Scalar.FiniteVolume.rightState g φ u i := by
  rw [FV1D.Nonuniform.rightState, slope_uniform, Scalar.FiniteVolume.rightState, smul_eq_mul]
  simp only [Mesh1D.uniform]
  ring

/-- FVN-U(b): on the uniform mesh the Burgers MUSCL step is the accepted B3 step `Rusanov.musclEulerStep`. -/
theorem musclStep_uniform (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (dt : ℝ) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) :
    musclStep (Mesh1D.uniform g dx hdx) dt φ u i = Rusanov.musclEulerStep g dx dt φ u i := by
  simp only [musclStep, face_eq, FV1D.Nonuniform.musclStep, FV1D.Nonuniform.update, leftState_uniform,
    rightState_uniform, Rusanov.musclEulerStep, Time.ForwardEuler.step, Scalar.FiniteVolume.musclRhs,
    Scalar.FiniteVolume.musclFlux, smul_eq_mul]
  simp only [Mesh1D.uniform]
  ring

/-! ### FVN-B: incremental form -/

/-- Coefficient of `u (next i) − u i` in cell `i`: `dt / w i · (a i − mean i) / 2`. -/
private def incrementC (m : Mesh1D I) (dt : ℝ) (u : I → ℝ) (i : I) : ℝ :=
  dt / m.width i * ((Rusanov.waveSpeed (u i) (u (m.grid.next i)) - (u i + u (m.grid.next i)) / 2) / 2)

/-- Coefficient of `u (next i) − u i` in cell `next i`: `dt / w (next i) · (a i + mean i) / 2`. -/
private def incrementD (m : Mesh1D I) (dt : ℝ) (u : I → ℝ) (i : I) : ℝ :=
  dt / m.width (m.grid.next i) * ((Rusanov.waveSpeed (u i) (u (m.grid.next i)) + (u i + u (m.grid.next i)) / 2) / 2)

private theorem firstOrderStep_eq_incrementalUpdate (m : Mesh1D I) (dt : ℝ) (u : I → ℝ) :
    firstOrderStep m dt u = incrementalUpdate m.grid (incrementC m dt u) (incrementD m dt u) u := by
  funext i
  simp only [firstOrderStep, FV1D.Nonuniform.firstOrderStep, FV1D.Nonuniform.update, face_eq,
    Rusanov.numericalFlux, Rusanov.eval, physicalFlux, incrementalUpdate, incrementC, incrementD,
    m.grid.next_prev, smul_eq_mul]
  ring

private theorem incrementC_nonneg (m : Mesh1D I) (dt : ℝ) (hdt : 0 ≤ dt) (u : I → ℝ) (i : I) :
    0 ≤ incrementC m dt u i := by
  have h := abs_le.mp (Rusanov.abs_mean_le_waveSpeed (u i) (u (m.grid.next i)))
  exact mul_nonneg (div_nonneg hdt (m.width_pos i).le) (by linarith)

private theorem incrementD_nonneg (m : Mesh1D I) (dt : ℝ) (hdt : 0 ≤ dt) (u : I → ℝ) (i : I) :
    0 ≤ incrementD m dt u i := by
  have h := abs_le.mp (Rusanov.abs_mean_le_waveSpeed (u i) (u (m.grid.next i)))
  exact mul_nonneg (div_nonneg hdt (m.width_pos _).le) (by linarith)

/-! ### FVN-B -/

/-- FVN-B (a): under the cell CFL condition `dt (a (prev i) + a i) ≤ w i` the first-order Burgers step keeps the
bounds `[lo, hi]`. -/
theorem firstOrderStep_mem (m : Mesh1D I) (dt : ℝ) (hdt : 0 ≤ dt) (lo hi : ℝ) (u : I → ℝ)
    (hu : u ∈ boundedStates lo hi)
    (hcfl : ∀ i, dt * (Rusanov.waveSpeed (u (m.grid.prev i)) (u (m.grid.next (m.grid.prev i))) +
      Rusanov.waveSpeed (u i) (u (m.grid.next i))) ≤ m.width i) :
    firstOrderStep m dt u ∈ boundedStates lo hi := by
  rw [firstOrderStep_eq_incrementalUpdate]
  intro i
  have hw := m.width_pos i
  have hr : 0 ≤ dt / m.width i := div_nonneg hdt hw.le
  have b1 := abs_le.mp (Rusanov.abs_mean_le_waveSpeed (u i) (u (m.grid.next i)))
  have b2 := abs_le.mp (Rusanov.abs_mean_le_waveSpeed (u (m.grid.prev i)) (u (m.grid.next (m.grid.prev i))))
  have hc := hcfl i
  rw [m.grid.next_prev] at b2 hc
  have hsum : dt / m.width i * (Rusanov.waveSpeed (u (m.grid.prev i)) (u i) +
      Rusanov.waveSpeed (u i) (u (m.grid.next i))) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hw]
    exact hc
  refine incrementalUpdate_bounds m.grid _ _ u lo hi i (incrementC_nonneg m dt hdt u i)
    (incrementD_nonneg m dt hdt u (m.grid.prev i)) ?_ (fun j => (hu j).1) (fun j => (hu j).2)
  simp only [incrementC, incrementD, m.grid.next_prev]
  linarith [mul_le_mul_of_nonneg_left b1.1 hr, mul_le_mul_of_nonneg_left b2.2 hr]

/-- FVN-B (b): under the face CFL condition `dt · a i ≤ min (w i) (w (next i))` the first-order Burgers step does
not increase the total variation. -/
theorem firstOrderStep_totalVariation_le [Fintype I] (m : Mesh1D I) (dt : ℝ) (hdt : 0 ≤ dt) (u : I → ℝ)
    (hcfl : ∀ i, dt * Rusanov.waveSpeed (u i) (u (m.grid.next i)) ≤ min (m.width i) (m.width (m.grid.next i))) :
    totalVariation m.grid (firstOrderStep m dt u) ≤ totalVariation m.grid u := by
  rw [firstOrderStep_eq_incrementalUpdate]
  refine incrementalUpdate_totalVariation_le m.grid _ _ u (incrementC_nonneg m dt hdt u)
    (incrementD_nonneg m dt hdt u) fun i => ?_
  have hmin : 0 < min (m.width i) (m.width (m.grid.next i)) := lt_min (m.width_pos i) (m.width_pos _)
  have b := abs_le.mp (Rusanov.abs_mean_le_waveSpeed (u i) (u (m.grid.next i)))
  have hc : 0 ≤ (Rusanov.waveSpeed (u i) (u (m.grid.next i)) - (u i + u (m.grid.next i)) / 2) / 2 := by linarith
  have hd : 0 ≤ (Rusanov.waveSpeed (u i) (u (m.grid.next i)) + (u i + u (m.grid.next i)) / 2) / 2 := by linarith
  have h1 : dt / m.width i ≤ dt / min (m.width i) (m.width (m.grid.next i)) :=
    div_le_div_of_nonneg_left hdt hmin (min_le_left _ _)
  have h2 : dt / m.width (m.grid.next i) ≤ dt / min (m.width i) (m.width (m.grid.next i)) :=
    div_le_div_of_nonneg_left hdt hmin (min_le_right _ _)
  have h3 : dt / min (m.width i) (m.width (m.grid.next i)) * Rusanov.waveSpeed (u i) (u (m.grid.next i)) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hmin]
    exact hcfl i
  simp only [incrementC, incrementD]
  linarith [mul_le_mul_of_nonneg_right h1 hc, mul_le_mul_of_nonneg_right h2 hd]

/-! ### FVN-MB -/

/-- The Burgers MUSCL step is the scalar MUSCL step of FVN-M with the B0 Rusanov flux. -/
private theorem musclStep_eq (m : Mesh1D I) (dt : ℝ) (φ : ℝ → ℝ → ℝ) :
    musclStep m dt φ = FV1D.Nonuniform.musclStep m Rusanov.numericalFlux.eval φ dt := by
  rw [musclStep, face_eq]

/-- `θ x / s ≤ x / w` when `θ w / s ≤ 1`. -/
private theorem theta_div_le (θ x w s : ℝ) (hx : 0 ≤ x) (hw : 0 < w) (h : θ * (w / s) ≤ 1) :
    θ * (x / s) ≤ x / w := by
  have e : θ * (x / s) = θ * (w / s) * (x / w) := by
    rw [mul_assoc, div_mul_div_comm, mul_comm w x, mul_div_mul_right _ _ hw.ne']
  rw [e]
  exact mul_le_of_le_one_left (div_nonneg hx hw.le) h

/-- `8 · dt · A ≤ w` gives `dt · (4A / w) ≤ 1/2`. -/
private theorem half_of_eight (dt A w : ℝ) (hw : 0 < w) (hcfl : 8 * dt * A ≤ w) : dt * (4 * A / w) ≤ 1 / 2 := by
  rw [← mul_div_assoc, div_le_iff₀ hw]
  linarith

/-- FVN-MB, one Forward-Euler step: bounds. -/
private theorem musclStep_mem (m : Mesh1D I) (dt lo hi : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ m.width i) (u : I → ℝ)
    (hu : u ∈ boundedStates lo hi) : musclStep m dt φ u ∈ boundedStates lo hi := by
  rw [musclStep_eq]
  refine FV1D.Nonuniform.musclStep_mem m φ θ hφ hr lo hi u hu Rusanov.numericalFlux Rusanov.monotone _ _
    (Rusanov.lipschitzOnBounds lo hi) dt hdt fun i => ?_
  have hA : 0 ≤ 2 * max |lo| |hi| := mul_nonneg zero_le_two ((abs_nonneg lo).trans (le_max_left _ _))
  have hw := m.width_pos i
  have h1 := theta_div_le θ (2 * max |lo| |hi|) (m.width i) _ hA hw
    (FV1D.Nonuniform.meshRatio_p_le_one m θ hr i)
  have hq := FV1D.Nonuniform.meshRatio_q_le_one m θ hr (m.grid.prev i)
  rw [m.grid.next_prev] at hq
  have h2 := theta_div_le θ (2 * max |lo| |hi|) (m.width i) _ hA hw hq
  have hle : (2 * max |lo| |hi| + 2 * max |lo| |hi|) / m.width i +
      θ * (2 * max |lo| |hi| / (m.width i + m.width (m.grid.next i)) +
        2 * max |lo| |hi| / (m.width (m.grid.prev i) + m.width i)) ≤ 2 * (4 * max |lo| |hi| / m.width i) := by
    have e1 : (2 * max |lo| |hi| + 2 * max |lo| |hi|) / m.width i = 2 * (2 * max |lo| |hi| / m.width i) := by ring
    have e2 : 2 * (4 * max |lo| |hi| / m.width i) = 4 * (2 * max |lo| |hi| / m.width i) := by ring
    rw [e1, e2, mul_add]
    linarith
  have h8 := half_of_eight dt (max |lo| |hi|) (m.width i) hw (hcfl i)
  linarith [mul_le_mul_of_nonneg_left hle hdt]

/-- FVN-MB, one Forward-Euler step: total variation. -/
private theorem musclStep_totalVariation_le [Fintype I] (m : Mesh1D I) (dt lo hi : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ m.width i)
    (u : I → ℝ) (hu : u ∈ boundedStates lo hi) :
    totalVariation m.grid (musclStep m dt φ u) ≤ totalVariation m.grid u := by
  rw [musclStep_eq]
  refine FV1D.Nonuniform.musclStep_totalVariation_le m φ θ hφ hr lo hi u hu Rusanov.numericalFlux
    Rusanov.monotone _ _ (Rusanov.lipschitzOnBounds lo hi) dt hdt fun i => ?_
  have hA : 0 ≤ 2 * max |lo| |hi| := mul_nonneg zero_le_two ((abs_nonneg lo).trans (le_max_left _ _))
  have hw := m.width_pos i
  have hw' := m.width_pos (m.grid.next i)
  have h1 := theta_div_le θ (2 * max |lo| |hi|) (m.width i) _ hA hw
    (FV1D.Nonuniform.meshRatio_p_le_one m θ hr i)
  have h2 := theta_div_le θ (2 * max |lo| |hi|) (m.width (m.grid.next i)) _ hA hw'
    (FV1D.Nonuniform.meshRatio_q_le_one m θ hr i)
  have hle : 2 * max |lo| |hi| / m.width i + 2 * max |lo| |hi| / m.width (m.grid.next i) +
      θ * (2 * max |lo| |hi| + 2 * max |lo| |hi|) / (m.width i + m.width (m.grid.next i)) ≤
        4 * max |lo| |hi| / m.width i + 4 * max |lo| |hi| / m.width (m.grid.next i) := by
    have e1 : θ * (2 * max |lo| |hi| + 2 * max |lo| |hi|) / (m.width i + m.width (m.grid.next i)) =
        θ * (2 * max |lo| |hi| / (m.width i + m.width (m.grid.next i))) +
          θ * (2 * max |lo| |hi| / (m.width i + m.width (m.grid.next i))) := by ring
    have e2 : 4 * max |lo| |hi| / m.width i = 2 * max |lo| |hi| / m.width i + 2 * max |lo| |hi| / m.width i := by
      ring
    have e3 : 4 * max |lo| |hi| / m.width (m.grid.next i) =
        2 * max |lo| |hi| / m.width (m.grid.next i) + 2 * max |lo| |hi| / m.width (m.grid.next i) := by ring
    rw [e1, e2, e3]
    linarith
  have h8 := half_of_eight dt (max |lo| |hi|) (m.width i) hw (hcfl i)
  have h8' := half_of_eight dt (max |lo| |hi|) (m.width (m.grid.next i)) hw' (hcfl _)
  linarith [mul_le_mul_of_nonneg_left hle hdt]

/-- FVN-MB: bounds and total variation after `n` Burgers MUSCL Forward-Euler steps under `8 · dt · A ≤ w i`. -/
theorem musclStep_iterate_stable [Fintype I] (m : Mesh1D I) (dt lo hi : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ m.width i)
    (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (n : ℕ) :
    (musclStep m dt φ)^[n] u ∈ boundedStates lo hi ∧
      totalVariation m.grid ((musclStep m dt φ)^[n] u) ≤ totalVariation m.grid u :=
  ⟨Time.SSP.iterate_mem _ _ (musclStep_mem m dt lo hi φ θ hφ hr hdt hcfl) u hu n,
    Time.SSP.iterate_le _ _ _ (musclStep_mem m dt lo hi φ θ hφ hr hdt hcfl)
      (musclStep_totalVariation_le m dt lo hi φ θ hφ hr hdt hcfl) u hu n⟩

/-- FVN-MB: bounds and total variation after `n` Burgers MUSCL SSPRK2 steps under `8 · dt · A ≤ w i`. -/
theorem musclSsprk2Step_iterate_stable [Fintype I] (m : Mesh1D I) (dt lo hi : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ m.width i)
    (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (n : ℕ) :
    (musclSsprk2Step m dt φ)^[n] u ∈ boundedStates lo hi ∧
      totalVariation m.grid ((musclSsprk2Step m dt φ)^[n] u) ≤ totalVariation m.grid u := by
  have hE := musclStep_mem m dt lo hi φ θ hφ hr hdt hcfl
  have hS := boundedStates_convex (I := I) lo hi
  have hT : ∀ v ∈ boundedStates lo hi, musclSsprk2Step m dt φ v ∈ boundedStates lo hi :=
    fun v hv => Time.SSP.ssprk2_mem _ _ hS hE v hv
  exact ⟨Time.SSP.iterate_mem _ _ hT u hu n, Time.SSP.iterate_le _ _ _ hT
    (fun v hv => Time.SSP.ssprk2_le _ _ _ (totalVariation_convexOn m.grid _ hS) hE
      (musclStep_totalVariation_le m dt lo hi φ θ hφ hr hdt hcfl) v hv) u hu n⟩

/-- FVN-MB: bounds and total variation after `n` Burgers MUSCL SSPRK3 steps under `8 · dt · A ≤ w i`. -/
theorem musclSsprk3Step_iterate_stable [Fintype I] (m : Mesh1D I) (dt lo hi : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ) (hdt : 0 ≤ dt) (hcfl : ∀ i, 8 * dt * max |lo| |hi| ≤ m.width i)
    (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (n : ℕ) :
    (musclSsprk3Step m dt φ)^[n] u ∈ boundedStates lo hi ∧
      totalVariation m.grid ((musclSsprk3Step m dt φ)^[n] u) ≤ totalVariation m.grid u := by
  have hE := musclStep_mem m dt lo hi φ θ hφ hr hdt hcfl
  have hS := boundedStates_convex (I := I) lo hi
  have hT : ∀ v ∈ boundedStates lo hi, musclSsprk3Step m dt φ v ∈ boundedStates lo hi :=
    fun v hv => Time.SSP.ssprk3_mem _ _ hS hE v hv
  exact ⟨Time.SSP.iterate_mem _ _ hT u hu n, Time.SSP.iterate_le _ _ _ hT
    (fun v hv => Time.SSP.ssprk3_le _ _ _ (totalVariation_convexOn m.grid _ hS) hE
      (musclStep_totalVariation_le m dt lo hi φ θ hφ hr hdt hcfl) v hv) u hu n⟩

end CFDLean.Burgers.Nonuniform
