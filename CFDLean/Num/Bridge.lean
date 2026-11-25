import CFDLean.Num.Boundary
import CFDLean.Geometry.MedianDual

/-! The M3 median-dual tetrahedral mesh (`CFDLean.MedianDual.MeshData`) as a weighted mesh with weights 1: closure of
vertices on no boundary face (P1-5.0b), the dual facets as gradient differences in 3D and 2D (P1-5.6), and
finite volume = Galerkin on M3 meshes (P1-5.7).

MC-N: definitions moved verbatim from JST_Paper_Lean `Paper1/Geometry/CFDBridge.lean` (namespace `Paper1` →
`CFDLean.Num`); proofs from `Paper1/Proofs/{Closure,DualFacets3}.lean`. -/
noncomputable section
open scoped BigOperators
namespace CFDLean.Num

def ofMeshData {n m : ℕ} (M : CFDLean.MedianDual.MeshData n m) : WMesh (Fin n) (Fin m) 3 where
  pos := M.position
  vert := M.vertex
  ω := fun _ => 1

def simplexOfPoints (p : CFDLean.MedianDual.Points) : Simplex 3 := ⟨p⟩

end CFDLean.Num

namespace CFDLean.Num.Internal

namespace Closure
open CFDLean.MedianDual

theorem det_edgeMat (p : Points) : (simplexOfPoints p).edgeMat.det = sixVolume p := by
  rw [Matrix.det_fin_three]
  simp [Simplex.edgeMat, simplexOfPoints, sixVolume, determinant, cross, CFDLean.Coordinates.dot_three]
  ring

theorem nondeg_of_pos (p : Points) (hp : 0 < sixVolume p) : (simplexOfPoints p).Nondeg := by
  unfold Simplex.Nondeg
  rw [det_edgeMat]
  exact hp.ne'

theorem vol_of_pos (p : Points) (hp : 0 < sixVolume p) : (simplexOfPoints p).vol = sixVolume p / 6 := by
  rw [Simplex.vol, det_edgeMat, abs_of_pos hp]
  norm_num [Nat.factorial]

theorem dot_smul_left' {d : ℕ} (c : ℝ) (u v : Vec d) : dot (c • u) v = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem faceVector_eq_grad (p : Points) (hp : 0 < sixVolume p) (j : Fin 4) :
    faceVector p j = (-(3 * (simplexOfPoints p).vol)) • (simplexOfPoints p).grad j := by
  apply vec_eq_of_dots (simplexOfPoints p) (nondeg_of_pos p hp)
  intro a
  have hg := (Simplex.calculus 3 (simplexOfPoints p) (nondeg_of_pos p hp)).2.1 j a 0
  rw [dot_smul_left', hg, vol_of_pos p hp]
  change dot (faceVector p j) (p a - p 0) = _
  fin_cases j <;> fin_cases a <;>
    simp [faceVector, triangle, cross, sixVolume, determinant, dot, Fin.sum_univ_three,
      CFDLean.Coordinates.dot_three] <;> ring

/-- The outward area vector of `ofMeshData M` is CFD_Lean's `faceArea`. -/
theorem facetVec_ofMeshData {n m : ℕ} (M : MeshData n m) (o : M.Occurrence) :
    (ofMeshData M).facetVec o = M.faceArea o := by
  have h := faceVector_eq_grad (M.points o.1) (M.positive o.1) o.2
  change (simplexOfPoints (M.points o.1)).facet o.2 = faceVector (M.points o.1) o.2
  rw [h, Simplex.facet]
  norm_num

theorem ofMeshData_valid {n m : ℕ} (M : MeshData n m) : (ofMeshData M).Valid :=
  ⟨fun _ => zero_le_one, fun t => nondeg_of_pos (M.points t) (M.positive t)⟩

theorem facetPaired {n m : ℕ} (M : MeshData n m) (hC : M.Conforming) (i : Fin n)
    (hb : ∀ o : M.Occurrence, M.faceCount (M.faceID o) = 1 → i ∉ M.faceID o) :
    (ofMeshData M).FacetPaired i := by
  classical
  have hfn : ∀ o, (ofMeshData M).facetNodes o = M.faceID o := fun o => rfl
  have partner : ∀ o : M.Occurrence, i ∈ M.faceID o → ∃ o', o' ≠ o ∧ M.faceID o' = M.faceID o := by
    intro o hi
    have hmem : o ∈ M.faceOccurrences (M.faceID o) := by simp [MeshData.faceOccurrences]
    have h1 : M.faceCount (M.faceID o) ≠ 1 := fun h => hb o h hi
    have hpos : 0 < M.faceCount (M.faceID o) := Finset.card_pos.mpr ⟨o, hmem⟩
    have hlt : 1 < (M.faceOccurrences (M.faceID o)).card := by
      unfold MeshData.faceCount at h1 hpos; omega
    obtain ⟨o', ho', hne⟩ := Finset.exists_mem_ne hlt o
    exact ⟨o', hne, (Finset.mem_filter.mp ho').2⟩
  have uniq : ∀ o o' o'' : M.Occurrence, o' ≠ o → o'' ≠ o → M.faceID o' = M.faceID o →
      M.faceID o'' = M.faceID o → o' = o'' := by
    intro o o' o'' h1 h2 h3 h4
    by_contra h5
    have hsub : ({o, o', o''} : Finset M.Occurrence) ⊆ M.faceOccurrences (M.faceID o) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp [MeshData.faceOccurrences, h3, h4]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
      Finset.card_pair h5] at hc
    have := hC.faceMultiplicity (M.faceID o)
    unfold MeshData.faceCount at this
    omega
  let σ : M.Occurrence → M.Occurrence := fun o =>
    if h : i ∈ M.faceID o then (partner o h).choose else o
  refine ⟨σ, fun o hi => ?_⟩
  rw [hfn] at hi
  have hσ : σ o = (partner o hi).choose := dite_eq_left hi
  have hspec := (partner o hi).choose_spec
  generalize (partner o hi).choose = o' at hσ hspec
  obtain ⟨hne, hf⟩ := hspec
  have hi' : i ∈ M.faceID o' := hf ▸ hi
  have hσ' : σ o' = o := by
    have h1 : σ o' = (partner o' hi').choose := dite_eq_left hi'
    obtain ⟨hne2, hf2⟩ := (partner o' hi').choose_spec
    rw [h1]
    exact uniq o' _ o hne2 (Ne.symm hne) hf2 hf.symm
  refine ⟨by rw [hσ, hσ'], by rw [hσ]; exact hne, by rw [hσ, hfn, hfn, hf], rfl, ?_⟩
  rw [hσ, facetVec_ofMeshData, facetVec_ofMeshData]
  exact M.faceArea_cancel hC o o' (Ne.symm hne) hf.symm

end Closure

/-- MC-N.P1-5.0b (JST `Paper1.Spec.P1_5_0b`, proof `Paper1.Proofs.p1_5_0b`). P1-5.0b (d = 3): in a conforming CFD_Lean tetrahedral mesh, a vertex on no boundary face is closed. -/
theorem _root_.CFDLean.Num.ofMeshData_closed :
    ∀ (n m : ℕ) (M : CFDLean.MedianDual.MeshData n m) (i : Fin n), M.Conforming →
      (∀ o : M.Occurrence, M.faceCount (M.faceID o) = 1 → i ∉ M.faceID o) →
      (ofMeshData M).Closed i := by
  intro n m M i hC hb
  exact Closure.closed_of_facetPaired _ i (Closure.facetPaired M hC i hb)

theorem localInterface_eq_grad (p : CFDLean.MedianDual.Points) (hp : 0 < CFDLean.MedianDual.sixVolume p)
    (i k : Fin 4) :
    CFDLean.MedianDual.localInterface p i k =
      ((simplexOfPoints p).vol / 4) • ((simplexOfPoints p).grad k - (simplexOfPoints p).grad i) := by
  rw [CFDLean.MedianDual.localInterface_eq, Closure.faceVector_eq_grad p hp i,
    Closure.faceVector_eq_grad p hp k]
  funext α
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- MC-N.P1-5.6 (JST `Paper1.Spec.P1_5_6`, proof `Paper1.Proofs.p1_5_6`). P1-5.6 (geometric dual facets): d = 3 (CFD_Lean flag triangles) and d = 2 (midpoint-centroid segment). -/
theorem _root_.CFDLean.Num.dualFacets_grad :
    (∀ (p : CFDLean.MedianDual.Points), 0 < CFDLean.MedianDual.sixVolume p →
      (simplexOfPoints p).Nondeg ∧ (simplexOfPoints p).vol = CFDLean.MedianDual.volume p ∧
      ∀ i k, CFDLean.MedianDual.localInterface p i k =
        ((simplexOfPoints p).vol / 4) • ((simplexOfPoints p).grad k - (simplexOfPoints p).grad i)) ∧
    (∀ (T : Simplex 2), T.Nondeg → ∀ i k, i ≠ k →
      dualFacet2 T i k = (T.vol / 3) • (T.grad k - T.grad i)) := by
  refine ⟨fun p hp => ⟨Closure.nondeg_of_pos p hp, ?_, fun i k => localInterface_eq_grad p hp i k⟩,
    fun T hT i k hik => dualFacet2_eq T hT i k hik⟩
  rw [Closure.vol_of_pos p hp]
  unfold CFDLean.MedianDual.volume
  rw [abs_of_pos hp]

/-- MC-N.P1-5.7 (JST `Paper1.Spec.P1_5_7`, proof `Paper1.Proofs.p1_5_7`). P1-5.7 (`prop:fv`, d = 3 on CFD_Lean meshes): the finite-volume residual over the real median-dual facets equals the Galerkin residual. -/
theorem _root_.CFDLean.Num.ofMeshData_fv_galerkin :
    ∀ (n m : ℕ) (κ : Type) [Fintype κ] (M : CFDLean.MedianDual.MeshData n m)
      (Fl : Fin m → Matrix κ (Fin 3) ℝ) (i : Fin n),
      (∑ t, ∑ a, ∑ b, if M.vertex t a = i then (Fl t).mulVec (CFDLean.MedianDual.localInterface (M.points t) a b)
        else 0) = (ofMeshData M).galerkinRes Fl i := by
  intro n m κ _ M Fl i
  unfold WMesh.galerkinRes
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : M.vertex t a = i
  · have hp := M.positive t
    have hb : ∀ b, (if M.vertex t a = i then
        (Fl t).mulVec (CFDLean.MedianDual.localInterface (M.points t) a b) else 0) =
        (Fl t).mulVec (((ofMeshData M).vol t / 4) • ((ofMeshData M).g t b - (ofMeshData M).g t a)) := by
      intro b
      rw [ite_eq_left ha, localInterface_eq_grad (M.points t) hp a b]
      rfl
    simp only [hb]
    have hlin : ∑ b, (Fl t).mulVec (((ofMeshData M).vol t / 4) • ((ofMeshData M).g t b - (ofMeshData M).g t a)) =
        (Fl t).mulVec (∑ b, ((ofMeshData M).vol t / 4) • ((ofMeshData M).g t b - (ofMeshData M).g t a)) := by
      have := map_sum (Matrix.mulVecLin (Fl t))
        (fun b => ((ofMeshData M).vol t / 4) • ((ofMeshData M).g t b - (ofMeshData M).g t a)) Finset.univ
      simp only [Matrix.mulVecLin_apply] at this
      exact this.symm
    have hsum : ∑ b, ((ofMeshData M).vol t / 4) • ((ofMeshData M).g t b - (ofMeshData M).g t a) =
        (-(ofMeshData M).vol t) • (ofMeshData M).g t a := by
      rw [← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [WMesh.g]
      rw [grad_sum, zero_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_neg, smul_smul, ← neg_smul]
      congr 1
      push_cast
      ring
    have hv : (ofMeshData M).vert t a = i := ha
    rw [hlin, hsum, Matrix.mulVec_smul, ite_eq_left hv]
    show _ = -(((1 : ℝ) * (ofMeshData M).vol t) • (Fl t).mulVec ((ofMeshData M).g t a))
    rw [one_mul, neg_smul]
  · have hv : ¬ (ofMeshData M).vert t a = i := ha
    simp [ha, hv]

end CFDLean.Num.Internal
