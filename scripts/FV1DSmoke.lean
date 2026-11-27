import CFDLean.Exec.FV1D

open CFDLean.Exec.FV1D

def main : IO Unit := do
  let burgersOld : Array Float := #[1, -2, 4]
  let scalar := stepArray burgers 0.5 1 0.125 burgersOld
  unless scalar == CFDLean.Exec.eulerStepArray 1 0.125 burgersOld do
    throw (IO.userError "Burgers dyadic smoke case differs from E0")
  let model := euler (1 : Float) 2 2 Float.abs Float.sqrt (fun a b => if a ≤ b then b else a)
  let old : Array (EulerState Float) := #[triple 1 2 3, triple 1 2 3]
  let result := stepArray model 0.5 1 0.125 old
  unless result.size == 2 && result.all (fun u => u 0 == 1 && u 1 == 2 && u 2 == 3) do
    throw (IO.userError "Euler constant-state smoke case failed")
