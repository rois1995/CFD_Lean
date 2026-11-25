import CFDLean.Papers.JST1.Mixed.SplitMean

/-! Frozen statements of item 3: `lem:splitmean` (lines 590-610), with the answers G2-G4 of `PAPER_GAPS.md`:
the sensor (hence `ε2`, `ε4`) is a fixed input inside the bracket `D`; the boundary part `bnd` of `Λ_i` is a given
split-independent input; positivity is assumed explicitly. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- P1-3.1: the mean over the splits of `Λ_i` under the first part of (A) is `Λ_i` on the assembled
coefficients. -/
def P1_3_1 : Prop :=
  ∀ (ι σ : Type) [Fintype ι] [Fintype σ] (d : ℕ) (ω : σ → ℝ) (χ : σ → ι → ι → Bool)
    (n : ι → ι → Vec d) (vb : ι → ι → Vec d) (cb : ι → ι → ℝ) (bnd : ι → ℝ) (i : ι),
    (∀ s, 0 ≤ ω s) → (∑ s, ω s) = 1 → (∀ k, (∃ s, χ s i k = true) → 0 < piShare ω χ i k) →
    (∀ k, (∀ s, χ s i k = false) → n i k = 0) →
    ∑ s, ω s * LamOn vb cb bnd (fun j k => nSplit ω χ n s j k) i = LamOn vb cb bnd n i

/-- P1-3.2: exact means of the linear nodal sums (Laplacian, sensor sums, counts), without (A). -/
def P1_3_2 : Prop :=
  ∀ (ι σ κ : Type) [Fintype ι] [Fintype σ] (ω : σ → ℝ) (χ : σ → ι → ι → Bool),
    (∀ (ut : ι → κ → ℝ) (Nstar : ι → Finset ι) (i : ι),
      ∑ s, ω s • (∑ k ∈ Nstar i, if χ s i k then ut k - ut i else 0) =
        ∑ k ∈ Nstar i, piShare ω χ i k • (ut k - ut i)) ∧
    (∀ (f : ι → ι → ℝ) (i : ι),
      ∑ s, ω s * (∑ k, if χ s i k then f i k else 0) = ∑ k, piShare ω χ i k * f i k)

/-- P1-3.3 (main): under (A) the mean over the splits of the dissipation of the pair `ik` is the dissipation with
the coefficient `π_ik^a Φ_ik λ̂_ik`. `D` is the split-independent bracket `ε2 (ũ_i - ũ_k) - ε4 (L_i - L_k)`. -/
def P1_3_3 : Prop :=
  ∀ (ι σ κ : Type) [Fintype ι] [Fintype σ] (d : ℕ) (ω : σ → ℝ) (χ : σ → ι → ι → Bool)
    (n e vb : ι → ι → Vec d) (cb : ι → ι → ℝ) (Lam : ι → ℝ) (a : ℝ) (D : κ → ℝ) (i k : ι),
    (∀ s, 0 ≤ ω s) → 0 < piShare ω χ i k →
    0 < lamHat (vb i k) (cb i k) (e i k) (n i k) → 0 < Lam i → 0 < Lam k →
    ∑ s, ω s • (if χ s i k then coefOn vb cb e Lam a (fun j l => nSplit ω χ n s j l) i k • D else 0) =
      ((piShare ω χ i k) ^ a * coefOn vb cb e Lam a n i k) • D

/-- P1-3.4: with share 1 (simplex mesh) the coefficient is that of eq. (jst). -/
def P1_3_4 : Prop :=
  ∀ (ι : Type) (d : ℕ) (n e vb : ι → ι → Vec d) (cb : ι → ι → ℝ) (Lam : ι → ℝ) (a p : ℝ) (i k : ι),
    p = 1 → p ^ a * coefOn vb cb e Lam a n i k = coefOn vb cb e Lam a n i k

end CFDLean.JST1.Spec
