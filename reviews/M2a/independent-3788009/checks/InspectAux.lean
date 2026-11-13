import AuxProvenance
import Lean
open Lean
run_cmd do
  let env ← getEnv
  for (n, i) in env.const2ModIdx.toList do
    if env.header.moduleNames[i.toNat]! == `AuxProvenance then
      if let some ci := env.checked.get.find? n then
        if ci matches .axiomInfo _ then logInfo m!"generated {n} unsafe={ci.isUnsafe}"
#print axioms ReviewerAux.proj
