import CFDLean.Exec.LimiterKernel

/-! Shared command-line parsing and formatting for the native 1D drivers. -/
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

/-- Parsed options: `--dump`, `--muscl`, the last `--limiter NAME`, the positional arguments. -/
structure Opts where
  dump : Bool := false
  muscl : Bool := false
  limiter : Option Limiter := none
  widths : Option String := none
  pos : List String := []

def parseArgs (allowWidths : Bool) : List String → Opts → Except String Opts
  | [], o => .ok { o with pos := o.pos.reverse }
  | "--dump" :: r, o => parseArgs allowWidths r { o with dump := true }
  | "--muscl" :: r, o => parseArgs allowWidths r { o with muscl := true }
  | ["--limiter"], _ => .error "--limiter needs a name"
  | "--limiter" :: s :: r, o =>
    match limiterOfName? s with
    | some L => parseArgs allowWidths r { o with limiter := some L }
    | none => .error s!"unknown limiter '{s}'"
  | "--widths" :: r, o =>
    if !allowWidths then parseArgs allowWidths r { o with pos := "--widths" :: o.pos }
    else if o.widths.isSome then .error "specify --widths only once"
    else match r with
      | [] => .error "--widths needs a comma-separated list"
      | csv :: rest => parseArgs allowWidths rest { o with widths := some csv }
  | s :: r, o => parseArgs allowWidths r { o with pos := s :: o.pos }

def schemeName (muscl : Option Limiter) : String :=
  match muscl with
  | none => "first-order"
  | some .none => "MUSCL, limiter = none (unlimited)"
  | some L => s!"MUSCL, limiter = {limiterName L}"

def uniformNote (muscl : Option Limiter) (cfl : Float) : String :=
  let range (c : Float) (s : String) : String :=
    s!"With real arithmetic bounds and total variation are proved for cfl <= {s}; this run is \
      {if c * cfl ≤ 1 then "inside" else "outside"} that range."
  match muscl with
  | none => range 2 "0.5"
  | some .none => "No bounds and no total-variation result are proved for the unlimited scheme; it can overshoot."
  | some L => range (limiterCfl L).1 (limiterCfl L).2
