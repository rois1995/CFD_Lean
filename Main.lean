import CFDLean.Exec.Kernel

/-! E0 driver: `burgers1d [N] [steps] [cfl] [--dump]`. Periodic domain `[0, 1)`, `dx = 1 / N`, initial cell values
`u_i = 0.5 + sin(2π (i + 0.5) dx)`, fixed `dt = cfl * dx / max |u0|`, `steps` SSPRK3 steps in `Float`. -/
open CFDLean.Exec

/-- Parse a decimal `d`, `d.f` or `.f` (no sign, no exponent). -/
def parseFloat? (s : String) : Option Float :=
  match s.splitOn "." with
  | [a] => a.toNat?.map Nat.toFloat
  | [a, b] => do
    let ia ← if a.isEmpty then some 0 else a.toNat?
    let ib ← if b.isEmpty then some 0 else b.toNat?
    pure (ia.toFloat + ib.toFloat / (10 : Float) ^ b.length.toFloat)
  | _ => none

/-- Scientific notation with 13 significant digits (core `toString` on `Float` prints only 6 decimals). -/
def sci (x : Float) : String :=
  if x == 0 then "0" else
    let a := Float.abs x
    let e := Float.floor (Float.log10 a)
    let ds := toString ((a / (10 : Float) ^ e * 1e12).round.toUInt64.toNat)
    let es := if e < 0 then s!"-{(-e).toUInt64}" else s!"{e.toUInt64}"
    s!"{if x < 0 then "-" else ""}{ds.take 1}.{ds.drop 1}e{es}"

def report (label : String) (dx : Float) (u : Array Float) : IO Unit :=
  IO.println s!"{label}: sum*dx = {sci (sumArray u * dx)}  min = {sci (minArray u)}  max = {sci (maxArray u)}  \
    TV = {sci (totalVariationArray u)}"

def main (args : List String) : IO UInt32 := do
  let n := (args[0]? >>= String.toNat?).getD 200
  let steps := (args[1]? >>= String.toNat?).getD 200
  let cfl := (args[2]? >>= parseFloat?).getD 0.4
  if n = 0 then
    IO.eprintln "N must be positive"
    return 1
  let dx := 1 / n.toFloat
  let pi := 2 * Float.acos 0
  let u0 := Array.ofFn fun i : Fin n => 0.5 + Float.sin (2 * pi * (i.val.toFloat + 0.5) * dx)
  let umax := Scalar.max (Float.abs (maxArray u0)) (Float.abs (minArray u0))
  let dt := cfl * dx / umax
  IO.println s!"N = {n}  steps = {steps}  cfl = {cfl}  dx = {sci dx}  dt = {sci dt}"
  report "initial" dx u0
  let u := run (ssprk3StepArray dx dt) steps u0
  report "final  " dx u
  IO.println s!"sum drift (final - initial) * dx = {sci ((sumArray u - sumArray u0) * dx)}"
  if args[3]? == some "--dump" then
    for v in u do
      IO.println (sci v)
  return 0
