import CFDLean.Schemes.Scalar.NumericalFlux

/-! Burgers B4-C: entropy certificates of a two-point flux in Tadmor's form, for an entropy variable `v` and an entropy
potential `ψ`. They are separate from the evaluator and from the other flux certificates. No relation between `v`, `ψ`
and a physical flux is assumed here. -/
noncomputable section
namespace CFDLean.Scalar

/-- B4-C: entropy-stability certificate (Tadmor) of a two-point flux for the entropy variable `v` and the entropy potential
`ψ`: `(v(b) - v(a)) F(a, b) ≤ ψ(b) - ψ(a)`. -/
def EntropyStable (v ψ : ℝ → ℝ) (nf : NumericalFlux) : Prop :=
  ∀ a b, (v b - v a) * nf.eval a b ≤ ψ b - ψ a

/-- B4-C: entropy-conservation certificate: equality in the entropy-stability condition. -/
def EntropyConservative (v ψ : ℝ → ℝ) (nf : NumericalFlux) : Prop :=
  ∀ a b, (v b - v a) * nf.eval a b = ψ b - ψ a

theorem EntropyConservative.entropyStable {v ψ : ℝ → ℝ} {nf : NumericalFlux} (h : EntropyConservative v ψ nf) :
    EntropyStable v ψ nf := fun a b => (h a b).le

end CFDLean.Scalar
