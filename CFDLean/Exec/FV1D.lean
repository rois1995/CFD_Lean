import CFDLean.Exec.Kernel

namespace CFDLean.Exec.FV1D

/-- State arithmetic and the two model functions consumed by one Rusanov step. -/
structure Model (α S : Type) where
  add : S → S → S
  sub : S → S → S
  scale : α → S → S
  flux : S → S
  speed : S → S → α

variable {α S : Type}

def face [Mul α] (M : Model α S) (half : α) (L R : S) : S :=
  M.sub (M.scale half (M.add (M.flux L) (M.flux R)))
    (M.scale (M.speed L R * half) (M.sub R L))

def stepArray [Mul α] [Div α] (M : Model α S) (half dx dt : α) (old : Array S) : Array S :=
  Array.ofFn fun i : Fin old.size =>
    let L := old[(i.val + old.size - 1) % old.size]'(pred_mod_lt i)
    let R := old[(i.val + 1) % old.size]'(succ_mod_lt i)
    M.sub old[i] (M.scale (dt/dx) (M.sub (face M half old[i] R) (face M half L old[i])))

@[simp] theorem size_stepArray [Mul α] [Div α] (M : Model α S) (half dx dt : α) (old : Array S) :
    (stepArray M half dx dt old).size = old.size := Array.size_ofFn

def burgers [Scalar α] : Model α α where
  add := (· + ·)
  sub := (· - ·)
  scale := (· * ·)
  flux := Scalar.burgersFlux
  speed := fun l r => Scalar.max (Scalar.abs l) (Scalar.abs r)

/-- Density, momentum density and total energy density, in the order used by M1's FV1D adapter. -/
abbrev EulerState (α : Type) := Fin 3 → α

def triple (r m e : α) : EulerState α := Fin.cases r (Fin.cases m (fun _ => e))

def pressure [Sub α] [Mul α] [Div α] (one two γ : α) (u : EulerState α) : α :=
  (γ-one)*(u 2 - u 1*u 1/(two*u 0))

def euler [Add α] [Sub α] [Mul α] [Div α] (one two γ : α) (abs sqrt : α → α)
    (max : α → α → α) : Model α (EulerState α) where
  add x y k := x k + y k
  sub x y k := x k - y k
  scale a x k := a*x k
  flux x :=
    let p := pressure one two γ x
    let v := x 1/x 0
    triple (x 1) (x 1*v+p) ((x 2+p)*v)
  speed x y :=
    let endpoint := fun u : EulerState α => abs (u 1/u 0) + sqrt (γ*pressure one two γ u/u 0)
    max (endpoint x) (endpoint y)

end CFDLean.Exec.FV1D
