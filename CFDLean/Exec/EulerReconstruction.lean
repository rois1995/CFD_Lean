import CFDLean.Exec.ReconstructedKernel

namespace CFDLean.Exec.FV1D

inductive EulerReconstruction where
  | minmod
  | weno
  deriving DecidableEq

/-- Select both traces together. A bad raw side returns both faces to the admissible cell mean. -/
def selectEulerPair {α : Type} (valid : EulerState α → Bool) (mean left right : EulerState α) :
    EulerState α × EulerState α :=
  if valid left && valid right then (left, right) else (mean, mean)

theorem selectEulerPair_valid {α : Type} (valid : EulerState α → Bool) (mean left right : EulerState α)
    (hmean : valid mean = true) :
    valid (selectEulerPair valid mean left right).1 = true ∧
    valid (selectEulerPair valid mean left right).2 = true := by
  unfold selectEulerPair
  split
  · exact Bool.and_eq_true_iff.mp (by assumption)
  · exact ⟨hmean, hmean⟩

/-- Conservative-component reconstruction. WENO uses the smoothness of each component separately. -/
def eulerComponent {α : Type} [Scalar α] [∀ n, OfNat α n] (scheme : EulerReconstruction) (ε : α)
    (widths : Array α) (u : Array (EulerState α))
    (i : Fin u.size) (k : Fin 3) : α × α :=
  let w (j : Fin u.size) := widthAt widths j.val
  match scheme with
    | .weno => wenoCell ε w (fun j => u[j] k) i
    | .minmod =>
      let l := prevIdx i
      let r := nextIdx i
      let backward := Scalar.two*w i/(w l+w i)*(u[i] k-u[l] k)
      let forward := Scalar.two*w i/(w i+w r)*(u[r] k-u[i] k)
      let halfSlope := Scalar.minmod backward forward / Scalar.two
      (u[i] k-halfSlope, u[i] k+halfSlope)

def eulerCell {α : Type} [Scalar α] [∀ n, OfNat α n] (scheme : EulerReconstruction) (ε : α)
    (valid : EulerState α → Bool) (widths : Array α) (u : Array (EulerState α))
    (i : Fin u.size) : EulerState α × EulerState α :=
  let component := eulerComponent scheme ε widths u i
  let ρ := component 0
  let m := component 1
  let e := component 2
  selectEulerPair valid u[i] (triple ρ.1 m.1 e.1) (triple ρ.2 m.2 e.2)

end CFDLean.Exec.FV1D
