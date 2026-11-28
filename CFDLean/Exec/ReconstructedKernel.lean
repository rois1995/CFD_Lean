import CFDLean.Discrete.Periodic.WenoStencil
import CFDLean.Exec.NonuniformKernel

namespace CFDLean.Exec

/-- Each cell reconstructs its left and right endpoints, reflecting geometry with the data. -/
def wenoCell {α : Type} [Add α] [Sub α] [Mul α] [Div α] [∀ n, OfNat α n] {n : Nat}
    (ε : α) (w u : Fin n → α) (i : Fin n) : α × α :=
  let edge (back ahead : Fin n → Fin n) := GradedWeno.edge ε
    (GradedWeno.gather back ahead w i) (GradedWeno.gather back ahead u i)
  (edge nextIdx prevIdx, edge prevIdx nextIdx)

/-- Assemble an oriented face flux once from the right endpoint of its owner and the left endpoint
of the successor. Widths and old states are indexed by the same periodic cell. -/
def reconstructedStep {α S : Type} [Mul α] [Div α] [Zero α] (M : FV1D.Model α S)
    (half dt : α) (widths : Array α) (old : Array S) (cell : Fin old.size → S × S) : Array S :=
  let endpoints := Vector.ofFn cell
  let flux := Vector.ofFn fun i : Fin old.size =>
    FV1D.face M half endpoints[i].2 endpoints[nextIdx i].1
  Array.ofFn fun i : Fin old.size =>
    M.sub old[i] (M.scale (dt / widthAt widths i.val) (M.sub flux[i] flux[prevIdx i]))

def burgersWenoStep {α : Type} [Scalar α] [∀ n, OfNat α n] (ε dt : α) (w u : Array α) : Array α :=
  reconstructedStep FV1D.burgers Scalar.half dt w u
    (wenoCell ε (fun i => widthAt w i.val) (fun i => u[i]))

def burgersWenoSsprk3 {α : Type} [Scalar α] [∀ n, OfNat α n] (ε dt : α) (w u : Array α) : Array α :=
  let step := burgersWenoStep ε dt w
  axpby Scalar.third u Scalar.twoThirds
    (step (axpby Scalar.threeQuarters u Scalar.quarter (step (step u))))

end CFDLean.Exec
