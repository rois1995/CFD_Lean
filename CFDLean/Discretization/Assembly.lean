import CFDLean.Flux.Roe.Flux

noncomputable section
namespace CFDLean.Assembly
open Coordinates
open scoped BigOperators

/-- One oriented record per interface; exterior pieces retain their own owner. -/
structure Interfaces (N E B : Type*) where
  tail : E → N
  head : E → N
  distinct : ∀ e, tail e ≠ head e
  owner : B → N

variable {N E B : Type*} [DecidableEq N] [Fintype E] [Fintype B]
variable {d k : ℕ}

def incidence (m : Interfaces N E B) (i : N) (e : E) : ℝ :=
  (if m.tail e = i then 1 else 0) - (if m.head e = i then 1 else 0)

def residual (m : Interfaces N E B) (f : E → Vector d) (g : B → Vector d) (i : N) : Vector d :=
  ∑ e, incidence m i e • f e + ∑ b, if m.owner b = i then g b else 0

/-- The same assembly on area vectors, before imposing geometric closure. -/
def metricDefect (m : Interfaces N E B) (S : E → Vector 3) (T : B → Vector 3) (i : N) : Vector 3 :=
  residual m S T i

omit [Fintype E] [Fintype B] in
theorem incidence_tail (m : Interfaces N E B) (e : E) : incidence m (m.tail e) e = 1 := by
  simp [incidence, Ne.symm (m.distinct e)]

omit [Fintype E] [Fintype B] in
theorem incidence_head (m : Interfaces N E B) (e : E) : incidence m (m.head e) e = -1 := by
  simp [incidence, m.distinct e]

omit [Fintype E] [Fintype B] in
theorem incidence_other (m : Interfaces N E B) (i : N) (e : E)
    (ht : m.tail e ≠ i) (hh : m.head e ≠ i) : incidence m i e = 0 := by
  simp [incidence, ht, hh]

omit [Fintype E] [Fintype B] in
theorem incidence_eq_one (m : Interfaces N E B) (i : N) (e : E) :
    incidence m i e = 1 ↔ i = m.tail e := by
  by_cases ht : m.tail e = i
  · subst i
    simp [incidence_tail]
  · by_cases hh : m.head e = i <;> norm_num [incidence, ht, hh, Ne.symm ht]

omit [Fintype E] [Fintype B] in
theorem incidence_eq_neg_one (m : Interfaces N E B) (i : N) (e : E) :
    incidence m i e = -1 ↔ i = m.head e := by
  by_cases hh : m.head e = i
  · subst i
    simp [incidence_head]
  · by_cases ht : m.tail e = i <;> norm_num [incidence, ht, hh, Ne.symm hh]

omit [Fintype E] [Fintype B] in
theorem incidence_sum [Fintype N] (m : Interfaces N E B) (e : E) : ∑ i, incidence m i e = 0 := by
  simp [incidence, Finset.sum_sub_distrib]

omit [Fintype E] [Fintype B] in
theorem incidence_smul (m : Interfaces N E B) (i : N) (e : E) (v : Vector d) :
    incidence m i e • v = (if m.tail e = i then v else 0) - (if m.head e = i then v else 0) := by
  by_cases ht : m.tail e = i <;> by_cases hh : m.head e = i <;> simp [incidence, ht, hh]

theorem residual_outgoing (m : Interfaces N E B) (f : E → Vector d) (g : B → Vector d) (i : N) :
    residual m f g i = (∑ e ∈ Finset.univ.filter (fun e => m.tail e = i), f e) -
      (∑ e ∈ Finset.univ.filter (fun e => m.head e = i), f e) +
      ∑ b ∈ Finset.univ.filter (fun b => m.owner b = i), g b := by
  classical
  simp only [residual, incidence_smul, Finset.sum_sub_distrib, Finset.sum_filter]

theorem global_balance [Fintype N] (m : Interfaces N E B) (f : E → Vector d) (g : B → Vector d) :
    ∑ i, residual m f g i = ∑ b, g b := by
  classical
  simp only [residual, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, incidence_sum, zero_smul, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_comm]
  simp

theorem residual_map (m : Interfaces N E B) (L : Vector d →ₗ[ℝ] Vector k)
    (f : E → Vector d) (g : B → Vector d) (i : N) :
    residual m (fun e => L (f e)) (fun b => L (g b)) i = L (residual m f g i) := by
  classical
  simp [residual, map_sum, apply_ite L]

/-- The accepted M1 physical transfer as a linear map of oriented area. -/
def physicalTransfer (γ : ℝ) (U : Conservative 3) : Vector 3 →ₗ[ℝ] StateCoordinates where
  toFun S := encode (physicalFlux γ U S)
  map_add' S T := by
    change encode (physicalFlux γ U (fun i => S i + T i)) = _
    rw [physicalFlux_add]
    funext i
    fin_cases i <;> rfl
  map_smul' a S := by
    change encode (physicalFlux γ U (fun i => a * S i)) = _
    rw [physicalFlux_mul]
    funext i
    fin_cases i <;> rfl

def roeTransfer (m : Interfaces N E B) (γ : ℝ) (U : N → Conservative 3) (S : E → Vector 3)
    (e : E) : StateCoordinates := encode (Roe.numericalFlux γ (U (m.tail e)) (U (m.head e)) (S e))

omit [DecidableEq N] [Fintype E] [Fintype B] in
theorem roeTransfer_consistency (m : Interfaces N E B) (γ : ℝ) (U : Conservative 3) (S : E → Vector 3) (e : E) :
    roeTransfer m γ (fun _ => U) S e = physicalTransfer γ U (S e) := by
  exact congrArg encode (Roe.numericalFlux_consistency γ U (S e))

omit [DecidableEq N] [Fintype E] [Fintype B] in
theorem roeTransfer_zero (m : Interfaces N E B) (γ : ℝ) (U : N → Conservative 3) (S : E → Vector 3)
    (e : E) (h : S e = 0) : roeTransfer m γ U S e = 0 := by
  unfold roeTransfer
  rw [h, Roe.numericalFlux_zero]
  funext i
  fin_cases i <;> rfl

theorem roe_global_balance [Fintype N] (m : Interfaces N E B) (γ : ℝ) (U : N → Conservative 3)
    (S : E → Vector 3) (g : B → StateCoordinates) :
    ∑ i, residual m (roeTransfer m γ U S) g i = ∑ b, g b := global_balance m _ g

theorem encoded_reverse (γ : ℝ) (U V : Conservative 3) (S : Vector 3) :
    encode (Roe.numericalFlux γ V U (-S)) = -encode (Roe.numericalFlux γ U V S) := by
  simp only [Roe.numericalFlux, encode_decode]
  exact Roe.roeFluxCoordinates_reverse γ (encode U) (encode V) S

/-- Independently evaluate each endpoint's outward interface orientation. -/
def outwardTransfer (m : Interfaces N E B) (γ : ℝ) (U : N → Conservative 3) (S : E → Vector 3)
    (i : N) (e : E) : StateCoordinates :=
  if m.tail e = i then encode (Roe.numericalFlux γ (U (m.tail e)) (U (m.head e)) (S e))
  else if m.head e = i then encode (Roe.numericalFlux γ (U (m.head e)) (U (m.tail e)) (-S e)) else 0

omit [Fintype E] [Fintype B] in
theorem outwardTransfer_eq (m : Interfaces N E B) (γ : ℝ) (U : N → Conservative 3) (S : E → Vector 3)
    (i : N) (e : E) : outwardTransfer m γ U S i e = incidence m i e • roeTransfer m γ U S e := by
  by_cases ht : m.tail e = i
  · subst i
    simp [outwardTransfer, incidence_tail, roeTransfer]
  · by_cases hh : m.head e = i
    · subst i
      simp [outwardTransfer, m.distinct e, incidence_head, encoded_reverse, roeTransfer]
    · simp [outwardTransfer, incidence, ht, hh]

def Interfaces.reverse (m : Interfaces N E B) (rev : E → Prop) [DecidablePred rev] : Interfaces N E B where
  tail e := if rev e then m.head e else m.tail e
  head e := if rev e then m.tail e else m.head e
  distinct e := by by_cases h : rev e <;> simp [h, m.distinct e, Ne.symm (m.distinct e)]
  owner := m.owner

omit [Fintype E] [Fintype B] in
theorem incidence_reverse (m : Interfaces N E B) (rev : E → Prop) [DecidablePred rev] (i : N) (e : E) :
    incidence (m.reverse rev) i e = if rev e then -incidence m i e else incidence m i e := by
  by_cases h : rev e <;> simp [incidence, Interfaces.reverse, h]

theorem residual_reverse (m : Interfaces N E B) (rev : E → Prop) [DecidablePred rev]
    (f : E → Vector d) (g : B → Vector d) (i : N) :
    residual (m.reverse rev) (fun e => if rev e then -f e else f e) g i = residual m f g i := by
  unfold residual
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : rev e <;> simp [incidence_reverse, h]

theorem roe_residual_reverse (m : Interfaces N E B) (rev : E → Prop) [DecidablePred rev]
    (γ : ℝ) (U : N → Conservative 3) (S : E → Vector 3) (g : B → StateCoordinates) (i : N) :
    residual (m.reverse rev) (roeTransfer (m.reverse rev) γ U (fun e => if rev e then -S e else S e)) g i =
      residual m (roeTransfer m γ U S) g i := by
  have hf : roeTransfer (m.reverse rev) γ U (fun e => if rev e then -S e else S e) =
      fun e => if rev e then -roeTransfer m γ U S e else roeTransfer m γ U S e := by
    funext e
    by_cases h : rev e <;> simp [roeTransfer, Interfaces.reverse, h, encoded_reverse]
  rw [hf, residual_reverse]

def Interfaces.reindex {N' E' B' : Type*} (m : Interfaces N E B)
    (n : N ≃ N') (e : E ≃ E') (b : B ≃ B') : Interfaces N' E' B' where
  tail j := n (m.tail (e.symm j))
  head j := n (m.head (e.symm j))
  distinct j := fun h => m.distinct (e.symm j) (n.injective h)
  owner j := n (m.owner (b.symm j))

theorem residual_reindex {N' E' B' : Type*} [DecidableEq N'] [Fintype E'] [Fintype B']
    (m : Interfaces N E B) (n : N ≃ N') (e : E ≃ E') (b : B ≃ B')
    (f : E → Vector d) (g : B → Vector d) (i : N) :
    residual (m.reindex n e b) (fun j => f (e.symm j)) (fun j => g (b.symm j)) (n i) = residual m f g i := by
  classical
  unfold residual
  congr 1
  · apply Fintype.sum_equiv e.symm
    intro j
    simp [incidence, Interfaces.reindex]
  · apply Fintype.sum_equiv b.symm
    intro j
    simp [Interfaces.reindex]

theorem roe_residual_reindex {N' E' B' : Type*} [DecidableEq N'] [Fintype E'] [Fintype B']
    (m : Interfaces N E B) (n : N ≃ N') (e : E ≃ E') (b : B ≃ B')
    (γ : ℝ) (U : N → Conservative 3) (S : E → Vector 3) (g : B → StateCoordinates) (i : N) :
    residual (m.reindex n e b)
      (roeTransfer (m.reindex n e b) γ (fun j => U (n.symm j)) (fun j => S (e.symm j)))
      (fun j => g (b.symm j)) (n i) = residual m (roeTransfer m γ U S) g i := by
  have hf : roeTransfer (m.reindex n e b) γ (fun j => U (n.symm j)) (fun j => S (e.symm j)) =
      fun j => roeTransfer m γ U S (e.symm j) := by
    funext j
    simp [roeTransfer, Interfaces.reindex]
  rw [hf, residual_reindex]

theorem constant_state_residual (m : Interfaces N E B) (γ : ℝ) (U : Conservative 3)
    (S : E → Vector 3) (T : B → Vector 3) (i : N) :
    residual m (roeTransfer m γ (fun _ => U) S) (fun b => physicalTransfer γ U (T b)) i =
      encode (physicalFlux γ U (metricDefect m S T i)) := by
  have hf : roeTransfer m γ (fun _ => U) S = fun e => physicalTransfer γ U (S e) := by
    funext e
    exact roeTransfer_consistency m γ U S e
  rw [hf, residual_map]
  rfl

theorem constant_state_closed (m : Interfaces N E B) (γ : ℝ) (U : Conservative 3)
    (S : E → Vector 3) (T : B → Vector 3) (i : N) (h : metricDefect m S T i = 0) :
    residual m (roeTransfer m γ (fun _ => U) S) (fun b => physicalTransfer γ U (T b)) i = 0 := by
  rw [constant_state_residual, h]
  exact (physicalTransfer γ U).map_zero

end CFDLean.Assembly
