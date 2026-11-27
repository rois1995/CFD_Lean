import CFDLean.Exec.NonuniformRefinement

/-! FVNA-T: the FVN guarantees transferred to the non-uniform array kernels of `CFDLean.Exec.NonuniformKernel`,
over the reals, through the refinement theorems of `CFDLean.Exec.NonuniformRefinement`.

Setting, as in the contract: `n ≥ 1` (`[NeZero n]`), `widths` and `u` real arrays of size `n`, every width positive.
Array entry `i` is periodic cell `(i : ZMod n)` and `meshOf widths` is the FVN mesh on `zmodGrid n`. The guarantees
are stated with the array diagnostics of E0: `sumArray` (weighted with `Array.zipWith (· * ·) widths`),
`totalVariationArray` and `EntriesBetween`; the contract's `n` steps are `run step k` (`n` is the array size).

- Bridges (supporting): `represents_samples`, `entriesBetween_samples_iff`, `totalVariationArray_samples`,
  `weightedSumArray_samples`, `meshOf_meshRatio_iff`.
- FVNA-T (a): `burgers_nonuniformStepArray_weighted_sum`, `nuLimiterEulerStepArray_weighted_sum`,
  `nuLimiterSsprk2StepArray_weighted_sum`, `nuLimiterSsprk3StepArray_weighted_sum`,
  `euler_nonuniformStepArray_weighted_sum`.
- FVNA-T (b): `burgers_nonuniformStepArray_bounds`, `burgers_nonuniformStepArray_totalVariation_le`.
- FVNA-T (c): `run_nuLimiterEulerStepArray_stable`, `run_nuLimiterSsprk2StepArray_stable`,
  `run_nuLimiterSsprk3StepArray_stable`. -/
noncomputable section
namespace CFDLean.Exec

open _root_.CFDLean.Scalar Periodic
open _root_.CFDLean.Exec.FV1D (samples samples_size samples_getElem samples_entries)
open scoped BigOperators

variable {n : ℕ} [NeZero n]

/-! ### Bridges between the array diagnostics and the periodic field -/

section Bridges

/-- Every residue is the cast of an index of an array of size `n`. -/
private theorem forall_zmod {S : Type} {P : ZMod n → Prop} {a : Array S} (hs : a.size = n)
    (h : ∀ i : Fin a.size, P (i.val : ZMod n)) (j : ZMod n) : P j := by
  have := h ⟨j.val, hs ▸ ZMod.val_lt j⟩
  simpa only [ZMod.natCast_zmod_val] using this

/-- A sum over `Fin n` of the residues is the sum over `ZMod n`. -/
private theorem sum_fin_natCast (f : ZMod n → ℝ) : ∑ i : Fin n, f (i.val : ZMod n) = ∑ j, f j := by
  refine Fintype.sum_bijective (fun i : Fin n => (i.val : ZMod n))
    ⟨fun a b h => ?_, fun j => ⟨⟨j.val, ZMod.val_lt j⟩, ZMod.natCast_zmod_val j⟩⟩ _ _ (fun _ => rfl)
  have h' := congrArg ZMod.val h
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h'
  exact Fin.ext h'

private theorem natCast_finGrid_next (i : Fin n) :
    ((((finGrid n).next i).val : ℕ) : ZMod n) = (zmodGrid n).next (i.val : ZMod n) := by
  rw [finGrid_next_val, ZMod.natCast_mod]
  simp [zmodGrid]

omit [NeZero n] in
/-- A stored field represents, in the E0 sense, the function `i ↦ U i` on `Fin n`. -/
theorem represents_samples (U : ZMod n → ℝ) : Represents (samples U) (fun i : Fin n => U (i.val : ZMod n)) :=
  ⟨samples_size U, fun i => samples_getElem U i.val _⟩

/-- The entries of a stored field lie in `[m, M]` exactly when the field is a bounded state. -/
theorem entriesBetween_samples_iff (m M : ℝ) (U : ZMod n → ℝ) :
    EntriesBetween m M (samples U) ↔ U ∈ FiniteVolume.boundedStates m M := by
  constructor
  · intro hb
    exact forall_zmod (samples_size U) fun i => by
      have h := hb i.val i.isLt
      rwa [samples_getElem] at h
  · intro hU i hi
    rw [samples_getElem]
    exact hU _

/-- The array total variation of a stored field is the periodic total variation on `zmodGrid n`. -/
theorem totalVariationArray_samples (U : ZMod n → ℝ) :
    totalVariationArray (samples U) = FiniteVolume.totalVariation (zmodGrid n) U := by
  rw [totalVariationArray_eq (represents_samples U)]
  simp only [FiniteVolume.totalVariation, natCast_finGrid_next]
  exact sum_fin_natCast (fun j => |U ((zmodGrid n).next j) - U j|)

/-- The width-weighted sum of a stored field, `∑ i, w[i] * u[i]`, is the FVN weighted sum on `meshOf widths`. -/
theorem weightedSumArray_samples (widths : Array ℝ) (hw : widths.size = n)
    (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) (U : ZMod n → ℝ) :
    sumArray (Array.zipWith (· * ·) widths (samples U)) = ∑ j, (meshOf widths hw hpos).width j * U j := by
  have hr : Represents (Array.zipWith (· * ·) widths (samples U))
      (fun i : Fin n => (meshOf widths hw hpos).width (i.val : ZMod n) * U (i.val : ZMod n)) := by
    refine ⟨by simp [hw], fun i => ?_⟩
    dsimp only
    rw [Array.getElem_zipWith, samples_getElem, ← widthAt_eq_meshOf widths hw hpos i.val i.isLt,
      widthAt_of_lt widths (by omega)]
  rw [sumArray_eq hr]
  exact sum_fin_natCast (fun j => (meshOf widths hw hpos).width j * U j)

/-- The mesh ratio `θ` of `meshOf widths`, written on the array: at every face `i`,
`θ * max w[i] w[i+1] ≤ w[i] + w[i+1]` (periodic indices). -/
theorem meshOf_meshRatio_iff (widths : Array ℝ) (hw : widths.size = n)
    (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) (θ : ℝ) :
    (meshOf widths hw hpos).MeshRatio θ ↔
      ∀ i : Fin widths.size, θ * max widths[i] widths[nextIdx i] ≤ widths[i] + widths[nextIdx i] := by
  have hwi : ∀ i : Fin widths.size, (meshOf widths hw hpos).width (i.val : ZMod n) = widths[i] := fun i => by
    rw [← widthAt_eq_meshOf widths hw hpos i.val (by omega), widthAt_of_lt widths i.isLt]
    rfl
  have key : ∀ i : Fin widths.size,
      (θ * max ((meshOf widths hw hpos).width (i.val : ZMod n))
          ((meshOf widths hw hpos).width ((meshOf widths hw hpos).grid.next (i.val : ZMod n))) ≤
        (meshOf widths hw hpos).width (i.val : ZMod n) +
          (meshOf widths hw hpos).width ((meshOf widths hw hpos).grid.next (i.val : ZMod n))) ↔
        θ * max widths[i] widths[nextIdx i] ≤ widths[i] + widths[nextIdx i] := fun i => by
    rw [meshOf_grid, ← natCast_nextIdx hw, hwi, hwi]
  constructor
  · intro h i
    exact (key i).1 (h _)
  · intro h
    exact forall_zmod hw fun i => (key i).2 (h i)

omit [NeZero n] in
/-- Running a step that stores `T` for `k` steps stores `T^[k]`. -/
private theorem run_samples {step : Array ℝ → Array ℝ} {T : (ZMod n → ℝ) → ZMod n → ℝ}
    (h : ∀ V, step (samples V) = samples (T V)) (k : ℕ) (U : ZMod n → ℝ) :
    run step k (samples U) = samples (T^[k] U) := by
  induction k generalizing U with
  | zero => rfl
  | succ k ih => rw [run, h, ih, Function.iterate_succ_apply]

/-- Generic transfer of `k`-step bounds and total variation from a periodic scheme `T` to a step that stores it. -/
private theorem run_stable_of {step : Array ℝ → Array ℝ} {T : (ZMod n → ℝ) → ZMod n → ℝ}
    (h : ∀ V, step (samples V) = samples (T V)) {m M : ℝ} (k : ℕ)
    (hT : ∀ U ∈ FiniteVolume.boundedStates m M, (T^[k] U) ∈ FiniteVolume.boundedStates m M ∧
      FiniteVolume.totalVariation (zmodGrid n) (T^[k] U) ≤ FiniteVolume.totalVariation (zmodGrid n) U)
    (u : Array ℝ) (hs : u.size = n) (hb : EntriesBetween m M u) :
    EntriesBetween m M (run step k u) ∧ totalVariationArray (run step k u) ≤ totalVariationArray u := by
  obtain ⟨U, rfl⟩ : ∃ U : ZMod n → ℝ, u = samples U := ⟨_, (samples_entries u hs).symm⟩
  rw [entriesBetween_samples_iff] at hb
  rw [run_samples h, entriesBetween_samples_iff, totalVariationArray_samples, totalVariationArray_samples]
  exact hT U hb

/-- The width-weighted sum on a mesh over `ZMod n`, as a linear functional. -/
private def weighted (msh : Mesh1D (ZMod n)) : (ZMod n → ℝ) →ₗ[ℝ] ℝ where
  toFun U := ∑ j, msh.width j * U j
  map_add' U V := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c U := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- The cell CFL bound of FVNA-T (c), on `meshOf widths`. -/
private theorem width_cfl (widths : Array ℝ) (hw : widths.size = n)
    (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) (dt m M : ℝ)
    (hcfl : ∀ (i : ℕ) (hi : i < widths.size), 8 * dt * max |m| |M| ≤ widths[i]) (j : ZMod n) :
    8 * dt * max |m| |M| ≤ (meshOf widths hw hpos).width j := by
  rw [meshOf_width]
  exact hcfl _ _

private theorem weighted_apply (msh : Mesh1D (ZMod n)) (U : ZMod n → ℝ) :
    weighted msh U = ∑ j, msh.width j * U j := rfl

end Bridges

/-! ### FVNA-T (a): conservation of the width-weighted sum -/

section Conservation

variable (widths : Array ℝ) (hw : widths.size = n) (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i])

include hw hpos

/-- FVNA-T (a), Burgers first order: the kernel keeps `∑ i, w[i] * u[i]`. -/
theorem burgers_nonuniformStepArray_weighted_sum (dt : ℝ) (u : Array ℝ) (hs : u.size = n) :
    sumArray (Array.zipWith (· * ·) widths (FV1D.nonuniformStepArray FV1D.burgers (1/2) dt widths u)) =
      sumArray (Array.zipWith (· * ·) widths u) := by
  obtain ⟨U, rfl⟩ : ∃ U : ZMod n → ℝ, u = samples U := ⟨_, (samples_entries u hs).symm⟩
  rw [burgers_nonuniform_refines dt widths hw hpos U _ rfl, weightedSumArray_samples widths hw hpos,
    weightedSumArray_samples widths hw hpos]
  exact _root_.CFDLean.FV1D.Nonuniform.firstOrderStep_weighted_sum _ _ dt U

/-- FVNA-T (a), Burgers MUSCL Forward Euler: for every limiter `L`, the kernel keeps `∑ i, w[i] * u[i]`. -/
theorem nuLimiterEulerStepArray_weighted_sum (L : Limiter) (dt : ℝ) (u : Array ℝ) (hs : u.size = n) :
    sumArray (Array.zipWith (· * ·) widths (nuLimiterEulerStepArray L dt widths u)) =
      sumArray (Array.zipWith (· * ·) widths u) := by
  obtain ⟨U, rfl⟩ : ∃ U : ZMod n → ℝ, u = samples U := ⟨_, (samples_entries u hs).symm⟩
  rw [nuLimiterEulerStepArray_refines L widths hw hpos U dt _ rfl, weightedSumArray_samples widths hw hpos,
    weightedSumArray_samples widths hw hpos]
  exact _root_.CFDLean.FV1D.Nonuniform.musclStep_weighted_sum _ _ _ dt U

/-- FVNA-T (a), Burgers MUSCL SSPRK2: for every limiter `L`, the kernel keeps `∑ i, w[i] * u[i]`. -/
theorem nuLimiterSsprk2StepArray_weighted_sum (L : Limiter) (dt : ℝ) (u : Array ℝ) (hs : u.size = n) :
    sumArray (Array.zipWith (· * ·) widths (nuLimiterSsprk2StepArray L dt widths u)) =
      sumArray (Array.zipWith (· * ·) widths u) := by
  obtain ⟨U, rfl⟩ : ∃ U : ZMod n → ℝ, u = samples U := ⟨_, (samples_entries u hs).symm⟩
  rw [nuLimiterSsprk2StepArray_refines L widths hw hpos U dt _ rfl, weightedSumArray_samples widths hw hpos,
    weightedSumArray_samples widths hw hpos, ← weighted_apply, ← weighted_apply]
  exact Time.SSP.ssprk2_linear _ _ (fun V => _root_.CFDLean.FV1D.Nonuniform.musclStep_weighted_sum _ _ _ dt V) U

/-- FVNA-T (a), Burgers MUSCL SSPRK3: for every limiter `L`, the kernel keeps `∑ i, w[i] * u[i]`. -/
theorem nuLimiterSsprk3StepArray_weighted_sum (L : Limiter) (dt : ℝ) (u : Array ℝ) (hs : u.size = n) :
    sumArray (Array.zipWith (· * ·) widths (nuLimiterSsprk3StepArray L dt widths u)) =
      sumArray (Array.zipWith (· * ·) widths u) := by
  obtain ⟨U, rfl⟩ : ∃ U : ZMod n → ℝ, u = samples U := ⟨_, (samples_entries u hs).symm⟩
  rw [nuLimiterSsprk3StepArray_refines L widths hw hpos U dt _ rfl, weightedSumArray_samples widths hw hpos,
    weightedSumArray_samples widths hw hpos, ← weighted_apply, ← weighted_apply]
  exact Time.SSP.ssprk3_linear _ _ (fun V => _root_.CFDLean.FV1D.Nonuniform.musclStep_weighted_sum _ _ _ dt V) U

/-- FVNA-T (a), Euler first order: for every `γ`, the kernel with the real Euler model keeps
`∑ i, w[i] * U[i] k` separately for each stored component `k`: density (`k = 0`), x-momentum (`k = 1`) and total
energy (`k = 2`), the order of `FV1D.EulerState` and `Euler1D.encode`. -/
theorem euler_nonuniformStepArray_weighted_sum (γ dt : ℝ) (old : Array (FV1D.EulerState ℝ)) (hs : old.size = n)
    (k : Fin 3) :
    sumArray (Array.zipWith (· * ·) widths
        ((FV1D.nonuniformStepArray (FV1D.euler 1 2 γ abs Real.sqrt max) (1/2) dt widths old).map (fun s => s k))) =
      sumArray (Array.zipWith (· * ·) widths (old.map (fun s => s k))) := by
  obtain ⟨V, rfl⟩ : ∃ V : ZMod n → FV1D.EulerState ℝ, old = samples V := ⟨_, (samples_entries old hs).symm⟩
  have hM : FV1D.euler 1 2 γ abs Real.sqrt max = ⟨(·+·), (·-·), (· • ·),
      (FV1D.euler (1 : ℝ) 2 γ abs Real.sqrt max).flux, (FV1D.euler (1 : ℝ) 2 γ abs Real.sqrt max).speed⟩ := rfl
  have hmap : ∀ W : ZMod n → FV1D.EulerState ℝ, (samples W).map (fun s => s k) = samples (fun j => W j k) :=
    fun W => by simp only [samples, Array.map_ofFn]; rfl
  rw [hM, nonuniformStepArray_compatible _ _ dt widths hw hpos V, hmap, hmap,
    weightedSumArray_samples widths hw hpos, weightedSumArray_samples widths hw hpos]
  have h := congrFun (_root_.CFDLean.FV1D.Nonuniform.firstOrderStep_weighted_sum (meshOf widths hw hpos)
    (_root_.CFDLean.FV1D.face (FV1D.euler (1 : ℝ) 2 γ abs Real.sqrt max).flux
      (FV1D.euler (1 : ℝ) 2 γ abs Real.sqrt max).speed) dt V) k
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

end Conservation

/-! ### FVNA-T (b): first-order Burgers bounds and total variation -/

section FirstOrder

variable (widths : Array ℝ) (hw : widths.size = n) (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i])

include hw hpos

/-- FVNA-T (b), bounds. If every entry of `u` lies in `[m, M]` and the FVN-B cell condition
`dt * (a (i-1) + a i) ≤ w[i]` holds in every cell, with `a i = max |u[i]| |u[i+1]|` the Rusanov speed of face `i`,
the first-order Burgers kernel keeps every entry in `[m, M]`. -/
theorem burgers_nonuniformStepArray_bounds (dt m M : ℝ) (hdt : 0 ≤ dt) (u : Array ℝ) (hs : u.size = n)
    (hb : EntriesBetween m M u)
    (hcfl : ∀ i : Fin u.size, dt * (Burgers.Rusanov.waveSpeed u[prevIdx i] u[i] +
      Burgers.Rusanov.waveSpeed u[i] u[nextIdx i]) ≤ widthAt widths i.val) :
    EntriesBetween m M (FV1D.nonuniformStepArray FV1D.burgers (1/2) dt widths u) := by
  obtain ⟨U, rfl⟩ : ∃ U : ZMod n → ℝ, u = samples U := ⟨_, (samples_entries u hs).symm⟩
  rw [entriesBetween_samples_iff] at hb
  rw [burgers_nonuniform_refines dt widths hw hpos U _ rfl, entriesBetween_samples_iff]
  refine Burgers.Nonuniform.firstOrderStep_mem (meshOf widths hw hpos) dt hdt m M U hb
    (forall_zmod (samples_size U) fun i => ?_)
  have h := hcfl i
  simp only [Fin.getElem_fin, samples_getElem] at h
  rw [natCast_prevIdx (samples_size U), natCast_nextIdx (samples_size U),
    widthAt_eq_meshOf widths hw hpos i.val (by simpa using i.isLt)] at h
  rw [meshOf_grid, Grid.next_prev]
  exact h

/-- FVNA-T (b), total variation. Under the FVN-B face condition `dt * a i ≤ min w[i] w[i+1]` at every face `i`, the
first-order Burgers kernel does not increase the total variation. -/
theorem burgers_nonuniformStepArray_totalVariation_le (dt : ℝ) (hdt : 0 ≤ dt) (u : Array ℝ) (hs : u.size = n)
    (hcfl : ∀ i : Fin u.size, dt * Burgers.Rusanov.waveSpeed u[i] u[nextIdx i] ≤
      min (widthAt widths i.val) (widthAt widths (nextIdx i).val)) :
    totalVariationArray (FV1D.nonuniformStepArray FV1D.burgers (1/2) dt widths u) ≤ totalVariationArray u := by
  obtain ⟨U, rfl⟩ : ∃ U : ZMod n → ℝ, u = samples U := ⟨_, (samples_entries u hs).symm⟩
  rw [burgers_nonuniform_refines dt widths hw hpos U _ rfl, totalVariationArray_samples,
    totalVariationArray_samples]
  refine Burgers.Nonuniform.firstOrderStep_totalVariation_le (meshOf widths hw hpos) dt hdt U
    (forall_zmod (samples_size U) fun i => ?_)
  have h := hcfl i
  simp only [Fin.getElem_fin, samples_getElem] at h
  rw [widthAt_eq_meshOf widths hw hpos i.val (by simpa using i.isLt),
    widthAt_eq_meshOf widths hw hpos (nextIdx i).val (by simpa using (nextIdx i).isLt),
    natCast_nextIdx (samples_size U)] at h
  rw [meshOf_grid]
  exact h

end FirstOrder

/-! ### FVNA-T (c): MUSCL bounds and total variation over `k` steps -/

section Muscl

variable (L : Limiter) (hL : L ≠ .none) (widths : Array ℝ) (hw : widths.size = n)
  (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) (hr : (meshOf widths hw hpos).MeshRatio L.theta)
  (dt m M : ℝ) (hdt : 0 ≤ dt) (hcfl : ∀ (i : ℕ) (hi : i < widths.size), 8 * dt * max |m| |M| ≤ widths[i])

include hL hr hdt hcfl

/-- FVNA-T (c), Forward Euler. For a limiter `L ≠ none` with mesh ratio `L.theta` on `meshOf widths`, `0 ≤ dt`,
initial entries in `[m, M]` and `8 * dt * max |m| |M| ≤ w[i]` in every cell, `k` steps of the MUSCL kernel keep every
entry in `[m, M]` and do not increase the total variation. -/
theorem run_nuLimiterEulerStepArray_stable (u : Array ℝ) (hs : u.size = n) (hb : EntriesBetween m M u) (k : ℕ) :
    EntriesBetween m M (run (nuLimiterEulerStepArray L dt widths) k u) ∧
      totalVariationArray (run (nuLimiterEulerStepArray L dt widths) k u) ≤ totalVariationArray u :=
  run_stable_of (fun V => nuLimiterEulerStepArray_refines L widths hw hpos V dt _ rfl) k
    (fun U hU => Burgers.Nonuniform.musclStep_iterate_stable (meshOf widths hw hpos) dt m M L.slopeFn L.theta
      (L.slopeBounded hL) hr hdt (width_cfl widths hw hpos dt m M hcfl) U hU k) u hs hb

/-- FVNA-T (c), SSPRK2: the statement of `run_nuLimiterEulerStepArray_stable` for the SSPRK2 kernel. -/
theorem run_nuLimiterSsprk2StepArray_stable (u : Array ℝ) (hs : u.size = n) (hb : EntriesBetween m M u) (k : ℕ) :
    EntriesBetween m M (run (nuLimiterSsprk2StepArray L dt widths) k u) ∧
      totalVariationArray (run (nuLimiterSsprk2StepArray L dt widths) k u) ≤ totalVariationArray u :=
  run_stable_of (fun V => nuLimiterSsprk2StepArray_refines L widths hw hpos V dt _ rfl) k
    (fun U hU => Burgers.Nonuniform.musclSsprk2Step_iterate_stable (meshOf widths hw hpos) dt m M L.slopeFn
      L.theta (L.slopeBounded hL) hr hdt (width_cfl widths hw hpos dt m M hcfl) U hU k) u hs hb

/-- FVNA-T (c), SSPRK3: the statement of `run_nuLimiterEulerStepArray_stable` for the SSPRK3 kernel. -/
theorem run_nuLimiterSsprk3StepArray_stable (u : Array ℝ) (hs : u.size = n) (hb : EntriesBetween m M u) (k : ℕ) :
    EntriesBetween m M (run (nuLimiterSsprk3StepArray L dt widths) k u) ∧
      totalVariationArray (run (nuLimiterSsprk3StepArray L dt widths) k u) ≤ totalVariationArray u :=
  run_stable_of (fun V => nuLimiterSsprk3StepArray_refines L widths hw hpos V dt _ rfl) k
    (fun U hU => Burgers.Nonuniform.musclSsprk3Step_iterate_stable (meshOf widths hw hpos) dt m M L.slopeFn
      L.theta (L.slopeBounded hL) hr hdt (width_cfl widths hw hpos dt m M hcfl) U hU k) u hs hb

end Muscl

/-! ### Checks

Every public theorem instantiated once with one cell (`n = 1`, where the seam reads the cell itself). -/

section Checks

private theorem one_cell_pos (w : ℝ) (hw : 0 < w) : ∀ (i : ℕ) (hi : i < #[w].size), 0 < #[w][i] := by
  intro i hi
  have h : i = 0 := by simpa using hi
  subst h
  simpa using hw

private theorem one_cell_entry (w : ℝ) (i : Fin #[w].size) : #[w][i] = w := by
  obtain ⟨i, hi⟩ := i
  have h : i = 0 := by simpa using hi
  subst h
  rfl

/-- One cell: every limiter has mesh ratio `L.theta`, because `L.theta ≤ 2`. -/
private theorem one_cell_meshRatio (L : Limiter) (w : ℝ) (hw : 0 < w) :
    (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)).MeshRatio L.theta := by
  rw [meshOf_meshRatio_iff]
  intro i
  rw [one_cell_entry, one_cell_entry, max_self]
  linarith [mul_le_mul_of_nonneg_right L.theta_le_two hw.le]

example (m M w : ℝ) (hw : 0 < w) (U : ZMod 1 → ℝ) :
    Represents (samples U) (fun i : Fin 1 => U (i.val : ZMod 1)) ∧
      (EntriesBetween m M (samples U) ↔ U ∈ FiniteVolume.boundedStates m M) ∧
      totalVariationArray (samples U) = FiniteVolume.totalVariation (zmodGrid 1) U ∧
      sumArray (Array.zipWith (· * ·) #[w] (samples U)) =
        ∑ j, (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)).width j * U j :=
  ⟨represents_samples U, entriesBetween_samples_iff m M U, totalVariationArray_samples U,
    weightedSumArray_samples #[w] rfl (one_cell_pos w hw) U⟩

example (L : Limiter) (w : ℝ) (hw : 0 < w) : (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)).MeshRatio L.theta :=
  one_cell_meshRatio L w hw

example (L : Limiter) (dt w a : ℝ) (hw : 0 < w) :
    sumArray (Array.zipWith (· * ·) #[w] (FV1D.nonuniformStepArray FV1D.burgers (1/2) dt #[w] #[a])) =
        sumArray (Array.zipWith (· * ·) #[w] #[a]) ∧
      sumArray (Array.zipWith (· * ·) #[w] (nuLimiterEulerStepArray L dt #[w] #[a])) =
        sumArray (Array.zipWith (· * ·) #[w] #[a]) ∧
      sumArray (Array.zipWith (· * ·) #[w] (nuLimiterSsprk2StepArray L dt #[w] #[a])) =
        sumArray (Array.zipWith (· * ·) #[w] #[a]) ∧
      sumArray (Array.zipWith (· * ·) #[w] (nuLimiterSsprk3StepArray L dt #[w] #[a])) =
        sumArray (Array.zipWith (· * ·) #[w] #[a]) :=
  ⟨burgers_nonuniformStepArray_weighted_sum (n := 1) #[w] rfl (one_cell_pos w hw) dt #[a] rfl,
    nuLimiterEulerStepArray_weighted_sum (n := 1) #[w] rfl (one_cell_pos w hw) L dt #[a] rfl,
    nuLimiterSsprk2StepArray_weighted_sum (n := 1) #[w] rfl (one_cell_pos w hw) L dt #[a] rfl,
    nuLimiterSsprk3StepArray_weighted_sum (n := 1) #[w] rfl (one_cell_pos w hw) L dt #[a] rfl⟩

/-- Euler, one cell: density, x-momentum and total energy, each separately. -/
example (γ dt w : ℝ) (hw : 0 < w) (s : FV1D.EulerState ℝ) :
    ∀ k : Fin 3, sumArray (Array.zipWith (· * ·) #[w]
        ((FV1D.nonuniformStepArray (FV1D.euler 1 2 γ abs Real.sqrt max) (1/2) dt #[w] #[s]).map
          (fun s => s k))) = sumArray (Array.zipWith (· * ·) #[w] (#[s].map (fun s => s k))) :=
  euler_nonuniformStepArray_weighted_sum (n := 1) #[w] rfl (one_cell_pos w hw) γ dt #[s] rfl

example (dt m M w a : ℝ) (hw : 0 < w) (hdt : 0 ≤ dt) (hb : EntriesBetween m M #[a])
    (hcell : ∀ i : Fin #[a].size, dt * (Burgers.Rusanov.waveSpeed #[a][prevIdx i] #[a][i] +
      Burgers.Rusanov.waveSpeed #[a][i] #[a][nextIdx i]) ≤ widthAt #[w] i.val)
    (hface : ∀ i : Fin #[a].size, dt * Burgers.Rusanov.waveSpeed #[a][i] #[a][nextIdx i] ≤
      min (widthAt #[w] i.val) (widthAt #[w] (nextIdx i).val)) :
    EntriesBetween m M (FV1D.nonuniformStepArray FV1D.burgers (1/2) dt #[w] #[a]) ∧
      totalVariationArray (FV1D.nonuniformStepArray FV1D.burgers (1/2) dt #[w] #[a]) ≤ totalVariationArray #[a] :=
  ⟨burgers_nonuniformStepArray_bounds (n := 1) #[w] rfl (one_cell_pos w hw) dt m M hdt #[a] rfl hb hcell,
    burgers_nonuniformStepArray_totalVariation_le (n := 1) #[w] rfl (one_cell_pos w hw) dt hdt #[a] rfl hface⟩

example (L : Limiter) (hL : L ≠ .none) (dt m M w a : ℝ) (hw : 0 < w) (hdt : 0 ≤ dt)
    (hcfl : ∀ (i : ℕ) (hi : i < #[w].size), 8 * dt * max |m| |M| ≤ #[w][i]) (hb : EntriesBetween m M #[a])
    (k : ℕ) :
    (EntriesBetween m M (run (nuLimiterEulerStepArray L dt #[w]) k #[a]) ∧
      totalVariationArray (run (nuLimiterEulerStepArray L dt #[w]) k #[a]) ≤ totalVariationArray #[a]) ∧
    (EntriesBetween m M (run (nuLimiterSsprk2StepArray L dt #[w]) k #[a]) ∧
      totalVariationArray (run (nuLimiterSsprk2StepArray L dt #[w]) k #[a]) ≤ totalVariationArray #[a]) ∧
    (EntriesBetween m M (run (nuLimiterSsprk3StepArray L dt #[w]) k #[a]) ∧
      totalVariationArray (run (nuLimiterSsprk3StepArray L dt #[w]) k #[a]) ≤ totalVariationArray #[a]) :=
  ⟨run_nuLimiterEulerStepArray_stable (n := 1) L hL #[w] rfl (one_cell_pos w hw) (one_cell_meshRatio L w hw)
      dt m M hdt hcfl #[a] rfl hb k,
    run_nuLimiterSsprk2StepArray_stable (n := 1) L hL #[w] rfl (one_cell_pos w hw) (one_cell_meshRatio L w hw)
      dt m M hdt hcfl #[a] rfl hb k,
    run_nuLimiterSsprk3StepArray_stable (n := 1) L hL #[w] rfl (one_cell_pos w hw) (one_cell_meshRatio L w hw)
      dt m M hdt hcfl #[a] rfl hb k⟩

end Checks

end CFDLean.Exec
