import Driver
import CFDLean.Exec.NonuniformKernel

open CFDLean.Exec

private def usageFV : String :=
  "usage: fv1d --model burgers [N] [steps] [cfl] [--muscl] [--limiter NAME] [--widths CSV] [--dump]\n\
   or:    fv1d --model euler [N] [--widths CSV] [--dump]"

private def parseWidths (n : Nat) (csv : String) : Except String (Array Float) := do
  let some ws := (csv.splitOn ",").mapM parseFloat? | throw "widths must be unsigned decimals"
  let widths := ws.toArray
  if widths.size != n then throw "expected one width per cell"
  if !widths.all (fun w => w.isFinite && w > 0) then throw "each width must be finite and positive"
  if Float.abs (widths.sum - 1) > 1e-12 then throw "widths must sum to one on the unit interval"
  return widths
