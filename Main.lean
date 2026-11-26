import CFDLean.Exec.Kernel
import CFDLean.Exec.MusclKernel
import CFDLean.Exec.LimiterKernel

/-! Burgers E0-X, the driver of `burgers1d [N] [steps] [cfl] [--muscl] [--limiter NAME] [--dump]`. Periodic domain
`[0, 1)`, `dx = 1 / N`, initial cell values `u_i = 0.5 + sin(2π (i + 0.5) dx)`, fixed `dt = cfl * dx / max |u0|`,
`steps` SSPRK3 steps of the kernel with `Float`: the first-order Rusanov scheme; with `--muscl` the unlimited
MUSCL-Rusanov scheme (central slope); with `--limiter NAME` the MUSCL-Rusanov scheme with that limiter. This file is
not verified.
The theorems of `CFDLean.Exec.Refinement` and `CFDLean.Exec.LimiterRefinement` are about the same kernels with real
arithmetic; nothing is proved about `Float` results. -/
open CFDLean.Exec

/-- Parse a decimal `d`, `d.f` or `.f` (no sign, no exponent). -/
def parseFloat? (s : String) : Option Float :=
  match s.splitOn "." with
  | [a] => a.toNat?.map Nat.toFloat
  | [a, b] => do
    if a.isEmpty && b.isEmpty then none
    let ia ← if a.isEmpty then some 0 else a.toNat?
    let ib ← if b.isEmpty then some 0 else b.toNat?
    pure (ia.toFloat + ib.toFloat / (10 : Float) ^ b.length.toFloat)
  | _ => none

/-- Scientific notation with 13 significant digits (core `toString` on `Float` prints only 6 decimals).
Not-a-number and the infinities are printed as `NaN`, `inf`, `-inf`. -/
def sci (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x < 0 then "-inf" else "inf")
  else if x == 0 then "0"
  else
    let a := Float.abs x
    let e0 := Float.floor (Float.log10 a)
    let m0 := (a / (10 : Float) ^ e0 * 1e12).round
    -- `log10` and the rounding can put the 13-digit mantissa one decade off; move it back
    let (m, e) := if m0 ≥ 1e13 then (m0 / 10, e0 + 1) else if m0 < 1e12 then (m0 * 10, e0 - 1) else (m0, e0)
    let ds := toString m.round.toUInt64.toNat
    let es := if e < 0 then s!"-{(-e).toUInt64}" else s!"{e.toUInt64}"
    s!"{if x < 0 then "-" else ""}{ds.take 1}.{ds.drop 1}e{es}"

def report (label : String) (dx : Float) (u : Array Float) : IO Unit :=
  IO.println s!"{label}: sum*dx = {sci (sumArray u * dx)}  min = {sci (minArray u)}  max = {sci (maxArray u)}  \
    TV = {sci (totalVariationArray u)}"

/-- Command-line name of a limiter. -/
def limiterName : Limiter → String
  | .none => "none"
  | .minmod => "minmod"
  | .mc => "mc"
  | .superbee => "superbee"
  | .vanLeer => "vanleer"
  | .vanAlbada => "vanalbada"

def limiterOfName? (s : String) : Option Limiter :=
  [Limiter.none, .minmod, .mc, .superbee, .vanLeer, .vanAlbada].find? (limiterName · == s)

/-- The bounds of a limiter are proved (real arithmetic) for `(4 + 2θ) · cfl ≤ 1`; `(4 + 2θ, "1/(4 + 2θ)")`. -/
def limiterCfl : Limiter → Float × String
  | .none => (0, "")
  | .minmod => (6, "1/6")
  | .vanAlbada => (6.5, "2/13")
  | _ => (8, "1/8")

def usage : String :=
  "usage: burgers1d [N] [steps] [cfl] [--muscl] [--limiter NAME] [--dump]\n  \
   N, steps: integers, N > 0 (defaults 200, 200)\n  \
   cfl: decimal such as 0.4 (default 0.4); dt = cfl * dx / max|u0|\n  \
   --muscl: MUSCL reconstruction, unlimited (central slope) unless --limiter is given (default: first-order scheme);\n  \
   \          before the limiter option this flag meant minmod: use --limiter minmod for that\n  \
   --limiter NAME: MUSCL with a limiter (implies --muscl); NAME is none, minmod, mc, superbee, vanleer or vanalbada\n  \
   --dump: print the final cell values"

/-- Parsed options: `--dump`, `--muscl`, the last `--limiter NAME`, the positional arguments. -/
structure Opts where
  dump : Bool := false
  muscl : Bool := false
  limiter : Option Limiter := none
  pos : List String := []

def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok { o with pos := o.pos.reverse }
  | "--dump" :: r, o => parseArgs r { o with dump := true }
  | "--muscl" :: r, o => parseArgs r { o with muscl := true }
  | ["--limiter"], _ => .error "--limiter needs a name"
  | "--limiter" :: s :: r, o =>
    match limiterOfName? s with
    | some L => parseArgs r { o with limiter := some L }
    | none => .error s!"unknown limiter '{s}'"
  | s :: r, o => parseArgs r { o with pos := s :: o.pos }

def main (args : List String) : IO UInt32 := do
  let bad (what : String) : IO UInt32 := do
    IO.eprintln s!"burgers1d: {what}\n{usage}"
    return 1
  let opts ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => return ← bad e
  let pos := opts.pos
  if pos.length > 3 then return ← bad "too many arguments"
  let some n := (match pos[0]? with | none => some 200 | some s => s.toNat?)
    | return ← bad "N is not a nonnegative integer"
  let some steps := (match pos[1]? with | none => some 200 | some s => s.toNat?)
    | return ← bad "steps is not a nonnegative integer"
  let some cfl := (match pos[2]? with | none => some 0.4 | some s => parseFloat? s)
    | return ← bad "cfl is not a decimal number"
  if n = 0 then return ← bad "N must be positive"
  -- `none`: first-order scheme; `some L`: MUSCL with limiter `L` (`Limiter.none`: unlimited)
  let muscl : Option Limiter := match opts.limiter with
    | some L => some L
    | none => if opts.muscl then some Limiter.none else none
  let dx := 1 / n.toFloat
  let pi := 2 * Float.acos 0
  let u0 := Array.ofFn fun i : Fin n => 0.5 + Float.sin (2 * pi * (i.val.toFloat + 0.5) * dx)
  let umax := Scalar.max (Float.abs (maxArray u0)) (Float.abs (minArray u0))
  let dt := cfl * dx / umax
  let scheme := match muscl with
    | none => "first-order"
    | some .none => "MUSCL, limiter = none (unlimited)"
    | some L => s!"MUSCL, limiter = {limiterName L}"
  IO.println s!"N = {n}  steps = {steps}  cfl = {cfl}  dx = {sci dx}  dt = {sci dt}  scheme = {scheme}"
  let range (c : Float) (s : String) : String :=
    s!"With real arithmetic bounds and total variation are proved for cfl <= {s}; this run is \
      {if c * cfl ≤ 1 then "inside" else "outside"} that range."
  let note := match muscl with
    | none => range 2 "0.5"
    | some .none => "No bounds and no total-variation result are proved for the unlimited scheme; it can overshoot."
    | some L => range (limiterCfl L).1 (limiterCfl L).2
  IO.println s!"note: Float arithmetic is not verified. {note}"
  report "initial" dx u0
  let step := match muscl with
    | none => ssprk3StepArray dx dt
    | some L => limiterSsprk3StepArray L dx dt
  let u := run step steps u0
  report "final  " dx u
  IO.println s!"sum drift (final - initial) * dx = {sci ((sumArray u - sumArray u0) * dx)}"
  if opts.dump then
    for v in u do
      IO.println (sci v)
  if u.any (fun v => !v.isFinite) then
    IO.eprintln "burgers1d: the final state has entries that are not finite (NaN or infinity)"
    return 2
  return 0
