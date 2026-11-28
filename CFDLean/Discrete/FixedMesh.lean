import CFDLean.Discrete.Assembly

/-! Conservative assembly of integrated transfers on a fixed control-volume mesh. -/
noncomputable section
namespace CFDLean.FixedMesh

open scoped BigOperators

variable {C I B S : Type*} [DecidableEq C] (m : Assembly.Interfaces C I B)
variable [AddCommGroup S]

/-- Scatter the single owner-oriented transfer with opposite signs at its endpoints. -/
def interior (f : I) (q : S) (i : C) : S :=
  (if m.tail f = i then q else 0) - (if m.head f = i then q else 0)

theorem interior_owner (f : I) (q : S) : interior m f q (m.tail f) = q := by
  simp [interior, Ne.symm (m.distinct f)]

theorem interior_neighbor (f : I) (q : S) : interior m f q (m.head f) = -q := by
  simp [interior, m.distinct f]

theorem interior_other (f : I) (q : S) (i : C) (ho : m.tail f ≠ i) (hn : m.head f ≠ i) :
    interior m f q i = 0 := by simp [interior, ho, hn]

variable [Fintype I] [Fintype B]

def residual (F : I → S) (G : B → S) (i : C) : S :=
  ∑ f, interior m f (F f) i + ∑ b, if m.owner b = i then G b else 0

/-- MD-C. The sum of the cell residuals contains only the realized boundary transfers. -/
theorem global_balance [Fintype C] (F : I → S) (G : B → S) :
    ∑ i, residual m F G i = ∑ b, G b := by
  simp only [residual, Finset.sum_add_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i b => if m.owner b = i then G b else 0)]
  simp [interior, Finset.sum_sub_distrib]

theorem closed_balance [Fintype C] [IsEmpty B] (F : I → S) (G : B → S) :
    ∑ i, residual m F G i = 0 := by simp [global_balance]

theorem coordinates_agree {n : ℕ} (F : I → Vector n) (G : B → Vector n) (i : C) :
    residual m F G i = Assembly.residual m F G i := by
  simp only [residual, Assembly.residual, Assembly.incidence_smul, interior]

theorem residual_reverse (rev : I → Prop) [DecidablePred rev] (F : I → S) (G : B → S) (i : C) :
    residual (m.reverse rev) (fun f => if rev f then -F f else F f) G i = residual m F G i := by
  unfold residual
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : rev f
  · by_cases ho : m.tail f = i <;> by_cases hn : m.head f = i <;>
      simp [interior, Assembly.Interfaces.reverse, h, ho, hn]
  · simp [interior, Assembly.Interfaces.reverse, h]

variable [Module ℝ S]

/-- MD-K. Equal-state consistency supplies `hF`; the boundary realization supplies `hG`. -/
theorem constant_defect {d : ℕ} (L : Vector d →ₗ[ℝ] S) (A : I → Vector d) (T : B → Vector d)
    (F : I → S) (G : B → S) (hF : ∀ f, F f = L (A f)) (hG : ∀ b, G b = L (T b)) (i : C) :
    residual m F G i = L (residual m A T i) := by
  simp [residual, interior, hF, hG, apply_ite L]

theorem constant_residual {d : ℕ} (L : Vector d →ₗ[ℝ] S) (A : I → Vector d) (T : B → Vector d)
    (F : I → S) (G : B → S) (hF : ∀ f, F f = L (A f)) (hG : ∀ b, G b = L (T b))
    (i : C) (closed : residual m A T i = 0) : residual m F G i = 0 := by
  rw [constant_defect m L A T F G hF hG, closed, map_zero]

/-- One Forward Euler update of a cell mean from its outward integrated residual. -/
def step (V : C → ℝ) (dt : ℝ) (U R : C → S) (i : C) : S := U i - (dt / V i) • R i

omit [DecidableEq C] in
theorem step_zero (V : C → ℝ) (U R : C → S) : step V 0 U R = U := by
  funext i
  simp [step]

omit [DecidableEq C] in
theorem step_zero_residual (V : C → ℝ) (dt : ℝ) (U R : C → S) (i : C) (h : R i = 0) :
    step V dt U R i = U i := by simp [step, h]

/-- MD-U. Only this step uses the positive volume certificate and a common timestep. -/
theorem step_balance [Fintype C] (V : C → ℝ) (hV : ∀ i, 0 < V i) (dt : ℝ) (U : C → S)
    (F : I → S) (G : B → S) :
    ∑ i, V i • step V dt U (residual m F G) i = (∑ i, V i • U i) - dt • ∑ b, G b := by
  have cancel (i : C) : V i * (dt / V i) = dt := by field_simp [(hV i).ne']
  simp only [step, smul_sub, smul_smul, cancel, Finset.sum_sub_distrib]
  rw [← Finset.smul_sum, global_balance]

theorem step_closed [Fintype C] [IsEmpty B] (V : C → ℝ) (hV : ∀ i, 0 < V i) (dt : ℝ)
    (U : C → S) (F : I → S) (G : B → S) :
    ∑ i, V i • step V dt U (residual m F G) i = ∑ i, V i • U i := by
  simp [step_balance m V hV]

end CFDLean.FixedMesh
