import CFDLean.Papers.JST1.Geometry.Dual2D
import CFDLean.Papers.JST1.Geometry.CFDBridge
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Frozen statements of item 5: `prop:fv` (lines 325-330, proof 1046-1054) and `lem:dissgeom`(a)-(c)
(lines 189-204, proof 898-918). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- P1-5.1: P1 simplex calculus. -/
def P1_5_1 : Prop :=
  ∀ (d : ℕ) (T : Simplex d), T.Nondeg →
    (∑ a, T.grad a = 0) ∧
    (∀ a b c, Num.dot (T.grad a) (T.x b - T.x c) = (if a = b then 1 else 0) - (if a = c then 1 else 0)) ∧
    (∑ a, outer (T.grad a) (T.x a) = 1) ∧ 0 < T.vol ∧ (∑ o, T.facet o = 0)

/-- P1-5.0a: a facet pairing at `i` makes `i` a closed (interior) vertex. -/
def P1_5_0a : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d) (i : ι),
    M.Valid → M.FacetPaired i → M.Closed i

/-- P1-5.0b (d = 3): in a conforming CFD_Lean tetrahedral mesh, a vertex on no boundary face is closed. -/
def P1_5_0b : Prop :=
  ∀ (n m : ℕ) (M : CFDLean.MedianDual.MeshData n m) (i : Fin n), M.Conforming →
    (∀ o : M.Occurrence, M.faceCount (M.faceID o) = 1 → i ∉ M.faceID o) →
    (ofMeshData M).Closed i

/-- P1-5.2 (`lem:dissgeom`(a)): `n·e = 2μ > 0`, and `ν` is a positive multiple of `e` with `|ν| = n·e/|e|`. -/
def P1_5_2 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d), M.Valid →
    (∀ i k, i ≠ k → Num.dot (M.n i k) (M.e i k) = 2 * M.mu i k) ∧
    (∀ i k, i ≠ k → (∃ T a b, M.vert T a = i ∧ M.vert T b = k ∧ 0 < M.ω T) →
      0 < M.mu i k ∧ (∃ t : ℝ, 0 < t ∧ M.nu i k = t • M.e i k) ∧
      len (M.nu i k) = Num.dot (M.n i k) (M.e i k) / len (M.e i k))

/-- P1-5.3 (`lem:dissgeom`(b)). -/
def P1_5_3 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d), M.Valid →
    (∀ i, ∑ k, outer (M.c i k) (M.e i k) = M.V i • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
    (∀ i, M.Closed i → ∑ k, outer (M.n i k) (M.e i k) = (2 * M.V i) • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
    (∑ i, ∑ k, outer (M.n i k) (M.e i k) = (2 * M.volΩ) • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
    (∑ i, M.V i = M.volΩ)

/-- P1-5.4 (`lem:dissgeom`(c), calibration). Sums over ordered pairs; each pair counts twice. -/
def P1_5_4 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d), M.Valid →
    (∀ i, M.Closed i → Matrix.trace (M.Gtensor M.nu i) = 2 * d * M.V i) ∧
    (∑ i, ∑ k, len (M.nu i k) * len (M.e i k) = 2 * d * M.volΩ) ∧
    (∀ i, M.Closed i → 2 * d * M.V i ≤ Matrix.trace (M.Gtensor M.n i)) ∧
    (∀ i, M.Closed i → (Matrix.trace (M.Gtensor M.n i) = 2 * d * M.V i ↔
      ∀ k, ∃ t : ℝ, 0 ≤ t ∧ M.n i k = t • M.e i k))

/-- P1-5.4b (Cartesian model): the `2d` neighbours `±h_α ê_α` with box-dual vectors `±(V/h_α) ê_α` give
`G(ν) = G(n) = 2V I`. -/
def P1_5_4b : Prop :=
  ∀ (d : ℕ) (V : ℝ) (h : Fin d → ℝ), 0 < V → (∀ α, 0 < h α) →
    let sgn : Bool → ℝ := fun s => if s then 1 else -1
    let E : Fin d × Bool → Vec d := fun p => (sgn p.2 * h p.1) • (Pi.single p.1 (1 : ℝ) : Vec d)
    let Y : Fin d × Bool → Vec d := fun p => (sgn p.2 * (V / h p.1)) • (Pi.single p.1 (1 : ℝ) : Vec d)
    (∀ p, WMesh.nuOf (Y p) (E p) = Y p) ∧
    ∑ p, (len (Y p) * len (E p)) • outer (WMesh.unit (E p)) (WMesh.unit (E p)) =
      (2 * V) • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- P1-5.5 (`prop:fv`, algebraic core): dual facet vectors `m_T (g_k - g_i)` turn the finite-volume residual of
constant element fluxes into the Galerkin residual. -/
def P1_5_5 : Prop :=
  ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
    (S : C → ι → ι → Vec d) (Fl : C → Matrix κ (Fin d) ℝ),
    (∀ T a b, S T (M.vert T a) (M.vert T b) = M.m T • (M.g T b - M.g T a)) →
    ∀ i, M.fvRes Fl S i = M.galerkinRes Fl i

/-- P1-5.6 (geometric dual facets): d = 3 (CFD_Lean flag triangles) and d = 2 (midpoint-centroid segment). -/
def P1_5_6 : Prop :=
  (∀ (p : CFDLean.MedianDual.Points), 0 < CFDLean.MedianDual.sixVolume p →
    (simplexOfPoints p).Nondeg ∧ (simplexOfPoints p).vol = CFDLean.MedianDual.volume p ∧
    ∀ i k, CFDLean.MedianDual.localInterface p i k =
      ((simplexOfPoints p).vol / 4) • ((simplexOfPoints p).grad k - (simplexOfPoints p).grad i)) ∧
  (∀ (T : Simplex 2), T.Nondeg → ∀ i k, i ≠ k →
    dualFacet2 T i k = (T.vol / 3) • (T.grad k - T.grad i))

/-- P1-5.7 (`prop:fv`, d = 3 on CFD_Lean meshes): the finite-volume residual over the real median-dual facets
equals the Galerkin residual. -/
def P1_5_7 : Prop :=
  ∀ (n m : ℕ) (κ : Type) [Fintype κ] (M : CFDLean.MedianDual.MeshData n m)
    (Fl : Fin m → Matrix κ (Fin 3) ℝ) (i : Fin n),
    (∑ t, ∑ a, ∑ b, if M.vertex t a = i then (Fl t).mulVec (CFDLean.MedianDual.localInterface (M.points t) a b)
      else 0) = (ofMeshData M).galerkinRes Fl i

/-- P1-5.8 (`prop:fv`, d = 2): the same with the segments `dualFacet2` on a valid triangle mesh. -/
def P1_5_8 : Prop :=
  ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (M : WMesh ι C 2)
    (Fl : C → Matrix κ (Fin 2) ℝ) (i : ι), M.Valid →
    (∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ b ≠ a then
      M.ω T • (Fl T).mulVec (dualFacet2 (M.simplex T) a b) else 0) = M.galerkinRes Fl i

end CFDLean.JST1.Spec
