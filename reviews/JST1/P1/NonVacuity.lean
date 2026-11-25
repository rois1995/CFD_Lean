import Paper1
import Paper1.Proofs.GeomBase
import Paper1.Proofs.Closure
import Paper1.Proofs.DissGeom

/-! Reviewer's non-vacuity checks for the P1 statements (independent review, not part of the build).
Compile with `lake env lean reviews/P1/NonVacuity.lean`. -/
noncomputable section
open scoped BigOperators
open NumCore Paper1

namespace Review

/-! ### 1. Admissible states exist (hypothesis of P1-1.x, 2.0, 2.5, 4.3b). -/

def rest (d : ℕ) : State d
  | .mass => 1
  | .momentum _ => 0
  | .energy => 1

theorem rest_admissible (d : ℕ) (g : Gas) : Admissible g (rest d) := by
  refine ⟨by simp [rho, rest], ?_⟩
  have h := g.one_lt_γ
  simp [pressure, rho, energy, mom, rest, dot]
  linarith

/-! ### 2. Gradient helper: a vector with the right edge dot products is the P1 gradient. -/

theorem grad_eq {d : ℕ} (T : Simplex d) (h : T.Nondeg) (a : Fin (d + 1)) (u : Vec d)
    (hu : ∀ b, dot u (T.x b - T.x 0) = (if a = b then 1 else 0) - (if a = 0 then 1 else 0)) :
    T.grad a = u := by
  apply Paper1.Proofs.vec_eq_of_dots T h
  intro b
  obtain ⟨-, hd, -⟩ := Paper1.Proofs.p1_5_1 d T h
  rw [hd a b 0, hu b]

/-! ### 3. A 2D mesh with an interior vertex: four right triangles around the origin (a diamond).
Vertex 4 is at the origin and is interior; vertices 0..3 are on the boundary. -/

def P : Fin 5 → Vec 2 := ![![1, 0], ![0, 1], ![-1, 0], ![0, -1], ![0, 0]]

def v0 : Fin 3 ↪ Fin 5 := ⟨fun a => ![4, 0, 1] a, by decide⟩
def v1 : Fin 3 ↪ Fin 5 := ⟨fun a => ![4, 1, 2] a, by decide⟩
def v2 : Fin 3 ↪ Fin 5 := ⟨fun a => ![4, 2, 3] a, by decide⟩
def v3 : Fin 3 ↪ Fin 5 := ⟨fun a => ![4, 3, 0] a, by decide⟩

def vt : Fin 4 → Fin 3 ↪ Fin 5 := ![v0, v1, v2, v3]

def diamond : WMesh (Fin 5) (Fin 4) 2 where
  pos := P
  vert := vt
  ω := fun _ => 1

/-- Explicit P1 gradients of the diamond cells. -/
def gv : Fin 4 → Fin 3 → Vec 2 :=
  ![![![-1, -1], ![1, 0], ![0, 1]],
    ![![1, -1], ![0, 1], ![-1, 0]],
    ![![1, 1], ![-1, 0], ![0, -1]],
    ![![-1, 1], ![0, -1], ![1, 0]]]

theorem diamond_nondeg (T : Fin 4) : (diamond.simplex T).Nondeg := by
  fin_cases T <;>
    simp [Simplex.Nondeg, Simplex.edgeMat, WMesh.simplex, diamond, Matrix.det_fin_two, vt, v0, v1, v2, v3, P]

theorem diamond_valid : diamond.Valid := ⟨fun _ => by simp [diamond], diamond_nondeg⟩

theorem diamond_g (T : Fin 4) (a : Fin 3) : diamond.g T a = gv T a := by
  unfold WMesh.g
  apply grad_eq _ (diamond_nondeg T)
  intro b
  fin_cases T <;> fin_cases a <;> fin_cases b <;>
    simp [dot, Fin.sum_univ_two, WMesh.simplex, diamond, vt, v0, v1, v2, v3, P, gv]

theorem diamond_vol (T : Fin 4) : diamond.vol T = 1 / 2 := by
  fin_cases T <;>
    simp [WMesh.vol, Simplex.vol, Simplex.edgeMat, WMesh.simplex, diamond, Matrix.det_fin_two, vt, v0, v1, v2,
      v3, P]

/-- The centre vertex is closed (the hypothesis `Closed` of P1-2.3, 5.3, 5.4 is satisfiable non-trivially). -/
theorem diamond_closed : diamond.Closed 4 := by
  intro k
  have hm : ∀ T, diamond.m T = 1 / 6 := by
    intro T; simp only [WMesh.m, diamond_vol]; norm_num
  simp only [WMesh.B, WMesh.c, WMesh.cW, diamond_g, hm]
  fin_cases k <;> funext α <;> fin_cases α <;>
    simp [Fin.sum_univ_succ, diamond, vt, v0, v1, v2, v3, gv] <;> norm_num

/-- A boundary vertex is not closed (so `Closed` is not trivially true). -/
theorem diamond_not_closed : ¬ diamond.Closed 0 := by
  intro h
  have hm : ∀ T, diamond.m T = 1 / 6 := by
    intro T; simp only [WMesh.m, diamond_vol]; norm_num
  have h0 := congrFun (h 0) 0
  simp only [WMesh.B, WMesh.c, WMesh.cW, diamond_g, hm] at h0
  simp [Fin.sum_univ_succ, diamond, vt, v0, v1, v2, v3, gv] at h0

/-- Consequence through the proved statements: P1-5.4 at the closed centre vertex is non-vacuous. -/
example : Matrix.trace (diamond.Gtensor diamond.nu 4) = 2 * 2 * diamond.V 4 := by
  have := (Paper1.Proofs.p1_5_4 (Fin 5) (Fin 4) 2 diamond diamond_valid).1 4 diamond_closed
  simpa using this

/-! ### 4. A 1D mesh with a facet pairing at the interior vertex (hypothesis of P1-5.0a). -/

def Q : Fin 3 → Vec 1 := ![![0], ![1], ![2]]
def w0 : Fin 2 ↪ Fin 3 := ⟨fun a => ![0, 1] a, by decide⟩
def w1 : Fin 2 ↪ Fin 3 := ⟨fun a => ![1, 2] a, by decide⟩
def wt : Fin 2 → Fin 2 ↪ Fin 3 := ![w0, w1]

def line : WMesh (Fin 3) (Fin 2) 1 where
  pos := Q
  vert := wt
  ω := fun _ => 1

theorem line_nondeg (T : Fin 2) : (line.simplex T).Nondeg := by
  fin_cases T <;> simp [Simplex.Nondeg, Simplex.edgeMat, WMesh.simplex, line, wt, w0, w1, Q] <;> norm_num

theorem line_valid : line.Valid := ⟨fun _ => by simp [line], line_nondeg⟩

def gl : Fin 2 → Vec 1 := ![![-1], ![1]]

theorem line_grad (T : Fin 2) (a : Fin 2) : (line.simplex T).grad a = gl a := by
  apply grad_eq _ (line_nondeg T)
  intro b
  fin_cases T <;> fin_cases a <;> fin_cases b <;>
    simp [dot, WMesh.simplex, line, wt, w0, w1, Q, gl] <;> norm_num

def swap : Fin 2 × Fin 2 → Fin 2 × Fin 2
  | (0, 0) => (1, 1)
  | (1, 1) => (0, 0)
  | p => p

theorem line_vol (T : Fin 2) : (line.simplex T).vol = 1 := by
  fin_cases T <;> simp [Simplex.vol, Simplex.edgeMat, WMesh.simplex, line, wt, w0, w1, Q] <;> norm_num

theorem line_facetVec (T o : Fin 2) : line.facetVec (T, o) = -(gl o) := by
  simp [WMesh.facetVec, Simplex.facet, line_vol, line_grad]

theorem line_paired : line.FacetPaired 1 := by
  refine ⟨swap, ?_⟩
  intro p hp
  fin_cases p
  · refine ⟨rfl, by decide, by decide, rfl, ?_⟩
    show line.facetVec (1, 1) = -line.facetVec (0, 0)
    rw [line_facetVec, line_facetVec]; funext x; fin_cases x; simp [gl]
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · refine ⟨rfl, by decide, by decide, rfl, ?_⟩
    show line.facetVec (0, 0) = -line.facetVec (1, 1)
    rw [line_facetVec, line_facetVec]; funext x; fin_cases x; simp [gl]

example : line.Closed 1 := Paper1.Proofs.p1_5_0a (Fin 3) (Fin 2) 1 line 1 line_valid line_paired

/-! ### 5. CFD_Lean (P1-5.0b): CFD_Lean proves `Controls.oneCell_conforming` and `Controls.two_cells_conforming`
(modules not built in this package, so not re-checked here). Neither example has a vertex on no boundary face, so
the interior-vertex case of P1-5.0b is not exercised by any concrete mesh. -/

end Review
