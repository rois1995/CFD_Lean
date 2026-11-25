import CFDLean.Discrete.Mesh
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Scalar-dissipation coefficients and their mean over the simplicial splits of mixed cells
(`lem:splitmean`). Generic over a finite vertex type `ι` and a finite split type `σ`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1
variable {ι σ : Type} [Fintype ι] [Fintype σ] {d : ℕ}

/-- Spectral radius on the edge projection: `λ̂(y) = |v̄·ν(y)| + c̄ |ν(y)|`, `ν(y) = (y·e/|e|²) e`. -/
def lamHat (vb : Vec d) (cb : ℝ) (e y : Vec d) : ℝ :=
  |Num.dot vb (WMesh.nuOf y e)| + cb * len (WMesh.nuOf y e)

/-- Spectral radius on the full vector (used in `Λ_i`). -/
def radFull (vb : Vec d) (cb : ℝ) (y : Vec d) : ℝ := |Num.dot vb y| + cb * len y

/-- Mavriplis-Jameson factors. -/
def psiF (Lam lh a : ℝ) : ℝ := (Lam / (4 * lh)) ^ a
def phiF (x y : ℝ) : ℝ := 4 * x * y / (x + y)

/-- Share of the splits that contain the pair. -/
def piShare (ω : σ → ℝ) (χ : σ → ι → ι → Bool) (i k : ι) : ℝ := ∑ s, if χ s i k then ω s else 0

/-- Closure (A), first part: the pair coefficient of a split that contains the pair. -/
def nSplit (ω : σ → ℝ) (χ : σ → ι → ι → Bool) (n : ι → ι → Vec d) (s : σ) (i k : ι) : Vec d :=
  if χ s i k then (piShare ω χ i k)⁻¹ • n i k else 0

/-- `Λ_i` on given pair coefficients `n'` with a given boundary part `bnd i` (split-independent, G3). -/
def LamOn (vb : ι → ι → Vec d) (cb : ι → ι → ℝ) (bnd : ι → ℝ) (n' : ι → ι → Vec d) (i : ι) : ℝ :=
  ∑ k, radFull (vb i k) (cb i k) (n' i k) + bnd i

/-- Coefficient `Φ λ̂` of the pair `ik` for pair coefficients `n'` and node values `Lam`. -/
def coefOn (vb : ι → ι → Vec d) (cb : ι → ι → ℝ) (e : ι → ι → Vec d) (Lam : ι → ℝ) (a : ℝ)
    (n' : ι → ι → Vec d) (i k : ι) : ℝ :=
  let lh := lamHat (vb i k) (cb i k) (e i k) (n' i k)
  phiF (psiF (Lam i) lh a) (psiF (Lam k) lh a) * lh

end CFDLean.JST1
