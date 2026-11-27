import Driver
/-! Burgers E0-X, the driver of `burgers1d [N] [steps] [cfl] [--muscl] [--limiter NAME] [--dump]`. Periodic domain
`[0, 1)`, `dx = 1 / N`, initial cell values `u_i = 0.5 + sin(2π (i + 0.5) dx)`, fixed `dt = cfl * dx / max |u0|`,
`steps` SSPRK3 steps of the kernel with `Float`: the first-order Rusanov scheme; with `--muscl` the unlimited
MUSCL-Rusanov scheme (central slope); with `--limiter NAME` the MUSCL-Rusanov scheme with that limiter. This file is
not verified.
The theorems of `CFDLean.Exec.Refinement` and `CFDLean.Exec.LimiterRefinement` are about the same kernels with real
arithmetic; nothing is proved about `Float` results. -/
open CFDLean.Exec

def usage : String :=
  "usage: burgers1d [N] [steps] [cfl] [--muscl] [--limiter NAME] [--dump]\n  \
   N, steps: integers, N > 0 (defaults 200, 200)\n  \
   cfl: decimal such as 0.4 (default 0.4); dt = cfl * dx / max|u0|\n  \
   --muscl: MUSCL reconstruction, unlimited (central slope) unless --limiter is given (default: first-order scheme);\n  \
     (before the limiter option this flag meant minmod: use --limiter minmod for that)\n  \
   --limiter NAME: MUSCL with a limiter (implies --muscl); NAME is none, minmod, mc, superbee, vanleer or vanalbada\n  \
   --dump: print the final cell values"

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
