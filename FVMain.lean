import Driver
import CFDLean.Exec.EulerReconstruction

open CFDLean.Exec

private def usageFV : String :=
  "usage: fv1d --model burgers [N] [steps] [cfl] [--weno | --muscl | --limiter NAME] [--widths CSV] [--dump]\n\
   or:    fv1d --model euler [N] [--muscl | --weno] [--widths CSV] [--dump]"

private def parseWidths (n : Nat) (csv : String) : Except String (Array Float) := do
  let some ws := (csv.splitOn ",").mapM parseFloat? | throw "widths must be unsigned decimals"
  let widths := ws.toArray
  if widths.size != n then throw "expected one width per cell"
  if !widths.all (fun w => w.isFinite && w > 0) then throw "each width must be finite and positive"
  if Float.abs (widths.sum - 1) > 1e-12 then throw "widths must sum to one on the unit interval"
  return widths

private def integral (w u : Array Float) : Float := (Array.zipWith (· * ·) w u).sum

private def centers (widths : Array Float) : Array Float := Id.run do
  let mut left := 0.0
  let mut xs := #[]
  for w in widths do
    xs := xs.push (left + w / 2)
    left := left + w
  return xs

private def runBurgers (n steps : Nat) (cfl : Float) (opts : Opts) (widths : Option (Array Float)) :
    IO UInt32 := do
  let muscl := opts.limiter.orElse fun _ => if opts.muscl then some Limiter.none else none
  let dx := 1 / n.toFloat
  let tau := 4 * Float.acos 0
  let u0 := match widths with
    | none => Array.ofFn fun i : Fin n => 0.5 + Float.sin (tau * (i.val.toFloat + 0.5) * dx)
    | some w => (centers w).map fun x => 0.5 + Float.sin (tau * x)
  let minWidth := widths.elim dx minArray
  let dt := cfl * minWidth / max (Float.abs (maxArray u0)) (Float.abs (minArray u0))
  let spacing := if widths.isSome then "min width" else "dx"
  let scheme := if opts.weno then "WENO-JS5" else schemeName muscl
  IO.println s!"N = {n}  steps = {steps}  cfl = {cfl}  {spacing} = {sci minWidth}  dt = {sci dt}  scheme = {scheme}"
  let reportState (label : String) (v : Array Float) := match widths with
    | none => report label dx v
    | some w => IO.println s!"{label}: integral = {sci (integral w v)}  min = {sci (minArray v)}  \
        max = {sci (maxArray v)}  TV = {sci (totalVariationArray v)}"
  let note := if opts.weno || widths.isSome then "" else " " ++ uniformNote muscl cfl
  IO.println s!"note: Float arithmetic is not verified.{note}"
  reportState "initial" u0
  let step := if opts.weno then burgersWenoSsprk3 1e-6 dt (widths.getD (Array.replicate n dx)) else match widths, muscl with
    | none, none => ssprk3StepArray dx dt
    | none, some l => limiterSsprk3StepArray l dx dt
    | some w, some l => nuLimiterSsprk3StepArray l dt w
    | some w, none =>
      let e := FV1D.nonuniformStepArray FV1D.burgers 0.5 dt w
      fun u => axpby Scalar.third u Scalar.twoThirds
        (e (axpby Scalar.threeQuarters u Scalar.quarter (e (e u))))
  let u := run step steps u0
  reportState "final  " u
  match widths with
  | none => IO.println s!"sum drift (final - initial) * dx = {sci ((sumArray u - sumArray u0) * dx)}"
  | some w => IO.println s!"integral drift = {sci (integral w u - integral w u0)}"
  if opts.dump then
    for v in u do IO.println (sci v)
  if u.any (fun v => !v.isFinite) then
    IO.eprintln "fv1d: non-finite final Burgers state"
    return 2
  return 0

private abbrev State := FV1D.EulerState Float

/-- Exact mean of the translated density wave, using the sine product form of the cosine difference. -/
private def densityWave (w xs : Array Float) (t : Float) : Array State :=
  let pi := 2 * Float.acos 0
  Array.zipWith (fun width x =>
    let rho := 1 + Float.sin (2 * pi * (x - 2 * t)) * (Float.sin (pi * width) / width) / 8
    FV1D.triple rho (2 * rho) (1 + 2 * rho)) w xs

private def components (u : State) : String := s!"{sci (u 0)} {sci (u 1)} {sci (u 2)}"

private def admissible (q : State) : Bool :=
  let p := FV1D.pressure 1 2 2 q
  (q 0).isFinite && (q 1).isFinite && (q 2).isFinite && q 0 > 0 && p.isFinite && p > 0

private def runEuler (n : Nat) (widths : Option (Array Float)) (scheme : Option FV1D.EulerReconstruction)
    (dump : Bool) : IO UInt32 := do
  let dx := 1 / n.toFloat
  let w := widths.getD (Array.replicate n dx)
  let xs := centers w
  let model := FV1D.euler (1 : Float) 2 2 Float.abs Float.sqrt max
  let minWidth := minArray w
  let finish := 0.125
  let store (q : State) : Vector Float 3 := #v[q 0, q 1, q 2]
  let mut cells := (densityWave w xs 0).map store
  let states (v : Array (Vector Float 3)) : Array State := v.map fun q k => q[k]
  let totals (v : Array State) : State := fun k => integral w (v.map (· k))
  IO.println s!"initial integrals = {components (totals (states cells))}"
  let mut t := 0.0
  let mut steps := 0
  while t < finish do
    let u := states cells
    let (dt?, advance) := match scheme with
      | none =>
        let step := match widths with
          | none => fun dt => FV1D.stepArray model 0.5 dx dt u
          | some ws => fun dt => FV1D.nonuniformStepArray model 0.5 dt ws u
        let speed := u.foldl (fun a q => max a (model.speed q q)) 0
        (some (min (finish - t) (0.4 * minWidth / speed)), step)
      | some method =>
        let endpoints := Vector.ofFn (FV1D.eulerCell method 1e-6 admissible w u)
        let speeds := Array.ofFn fun i : Fin u.size => model.speed endpoints[i].2 endpoints[nextIdx i].1
        (reconstructedEulerDt? (finish - t) minWidth speeds,
          fun dt => reconstructedStep model 0.5 dt w u (fun i => endpoints[i]))
    let some dt := dt? | do
      IO.eprintln "fv1d: invalid reconstructed Euler face speed"
      return 2
    if !dt.isFinite || t + dt <= t then
      IO.eprintln "fv1d: Euler timestep cannot advance time"
      return 2
    -- Evaluate the three components now so later steps do not repeatedly evaluate old states.
    cells := (advance dt).map store
    if cells.any (fun q => !admissible (fun k => q[k])) then
      IO.eprintln "fv1d: Euler step produced a non-finite or inadmissible state"
      return 2
    t := t + dt
    steps := steps + 1
  let u := states cells
  let exact := densityWave w xs t
  let errors : State := fun k => integral w (Array.zipWith (fun q ref => Float.abs (q k - ref k)) u exact)
  let reconstruction := match scheme with
    | none => ""
    | some .minmod => " / MUSCL-minmod"
    | some .weno => " / WENO-JS5"
  IO.println s!"Euler Rusanov{reconstruction} / Forward Euler  N = {n}  steps = {steps}  time = {sci t}"
  IO.println s!"final integrals = {components (totals u)}"
  IO.println s!"L1 errors = {components errors}"
  if dump then
    for q in u do IO.println (components q)
  return 0

def main (args : List String) : IO UInt32 := do
  let bad (msg : String) : IO UInt32 := do
    IO.eprintln s!"fv1d: {msg}\n{usageFV}"
    return 1
  let "--model" :: model :: rest := args | return ← bad "select a model"
  if model != "burgers" && model != "euler" then return ← bad s!"unknown model '{model}'"
  let opts ← match parseArgs rest {} with
    | .ok value => pure value
    | .error e => return ← bad e
  let pos := opts.pos
  let some n := pos[0]?.elim (some (if model == "burgers" then 200 else 4)) String.toNat?
    | return ← bad "N must be a positive integer"
  if n == 0 then return ← bad "N must be positive"
  let widths ← match opts.widths.mapM (parseWidths n) with
    | .ok value => pure value
    | .error e => return ← bad e
  if opts.weno && (opts.muscl || opts.limiter.isSome) then return ← bad "choose WENO or MUSCL with a limiter"
  if model == "euler" then
    if opts.limiter.any (· != .minmod) then return ← bad "Euler MUSCL supports the minmod limiter"
    let scheme := if opts.weno then some FV1D.EulerReconstruction.weno
      else if opts.muscl || opts.limiter.isSome then some .minmod else none
    if pos.length > 1 then return ← bad "Euler takes only the cell count"
    return ← runEuler n widths scheme opts.dump
  if pos.length > 3 then return ← bad "too many Burgers arguments"
  let some steps := pos[1]?.elim (some 200) String.toNat? | return ← bad "steps must be a nonnegative integer"
  let some cfl := pos[2]?.elim (some 0.4) parseFloat? | return ← bad "cfl must be an unsigned decimal"
  if !cfl.isFinite then return ← bad "cfl must be finite"
  runBurgers n steps cfl opts widths
