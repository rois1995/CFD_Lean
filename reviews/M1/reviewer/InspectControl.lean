import CompilerControl
import Lean

open Lean
run_cmd do
  let env ← getEnv
  for (n, idx) in env.const2ModIdx.toList do
    if env.header.moduleNames[idx.toNat]! == `CompilerControl then
      if let some ci := env.checked.get.find? n then
        if ci matches .axiomInfo _ then
          logInfo m!"CONTROL | {n} | unsafe={ci.isUnsafe}"
#print axioms M1Control.lengthSquared
#print axioms M1Control.productSum
