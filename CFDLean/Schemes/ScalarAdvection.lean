import CFDLean.Discrete.FixedMesh

/-! First-order scalar advection with a fixed velocity and integrated oriented fluxes. -/
noncomputable section
namespace CFDLean.ScalarAdvection

variable {d : ℕ} (v : Vector d)

/-- The area vector includes the face measure. -/
def flux (A : Vector d) (left right : ℝ) : ℝ :=
  let s := dotProduct v A
  s * (if 0 ≤ s then left else right)

theorem flux_consistent (A : Vector d) (k : ℝ) : flux v A k k = dotProduct v A * k := by
  simp [flux]

theorem flux_zero_speed (A : Vector d) (left right : ℝ) (h : dotProduct v A = 0) :
    flux v A left right = 0 := by simp [flux, h]

theorem flux_reverse (A : Vector d) (left right : ℝ) : flux v (-A) right left = -flux v A left right := by
  simp only [flux, dotProduct_neg]
  rcases lt_trichotomy (dotProduct v A) 0 with h | h | h
  · simp [not_le.mpr h, neg_nonneg.mpr h.le]
  · simp [h]
  · simp [h.le, not_le.mpr (neg_lt_zero.mpr h)]

variable {C I B : Type*} (m : Assembly.Interfaces C I B) (A : I → Vector d) (T : B → Vector d)

def interiorFlux (U : C → ℝ) (f : I) : ℝ := flux v (A f) (U (m.tail f)) (U (m.head f))

def boundaryFlux (U : C → ℝ) (g : B → ℝ) (b : B) : ℝ := flux v (T b) (U (m.owner b)) (g b)

variable [DecidableEq C] [Fintype I] [Fintype B]

def residual (U : C → ℝ) (g : B → ℝ) :=
  FixedMesh.residual m (interiorFlux v m A U) (boundaryFlux v m T U g)

private def physicalTransfer (k : ℝ) : Vector d →ₗ[ℝ] ℝ where
  toFun A := dotProduct v A * k
  map_add' a b := by simp [dotProduct_add, add_mul]
  map_smul' r a := by simp [dotProduct_smul, mul_assoc]

theorem constant_residual (k : ℝ) (i : C) (closed : FixedMesh.residual m A T i = 0) :
    residual v m A T (fun _ => k) (fun _ => k) i = 0 :=
  FixedMesh.constant_residual m (physicalTransfer v k) A T _ _
    (fun f => flux_consistent v (A f) k) (fun b => flux_consistent v (T b) k) i closed

theorem constant_step (k dt : ℝ) (V : C → ℝ) (i : C) (closed : FixedMesh.residual m A T i = 0) :
    FixedMesh.step V dt (fun _ => k) (residual v m A T (fun _ => k) (fun _ => k)) i = k :=
  FixedMesh.step_zero_residual V dt _ _ i (constant_residual v m A T k i closed)

variable [Fintype C] (U : C → ℝ) (g : B → ℝ)

theorem global_balance : ∑ i, residual v m A T U g i = ∑ b, boundaryFlux v m T U g b :=
  FixedMesh.global_balance m _ _

theorem step_balance (V : C → ℝ) (positive : ∀ i, 0 < V i) (dt : ℝ) :
    ∑ i, V i * FixedMesh.step V dt U (residual v m A T U g) i =
      (∑ i, V i * U i) - dt * ∑ b, boundaryFlux v m T U g b :=
  FixedMesh.step_balance m V positive dt U _ _

theorem step_closed [IsEmpty B] (V : C → ℝ) (positive : ∀ i, 0 < V i) (dt : ℝ) :
    ∑ i, V i * FixedMesh.step V dt U (residual v m A T U g) i = ∑ i, V i * U i :=
  FixedMesh.step_closed m V positive dt U _ _

end CFDLean.ScalarAdvection
