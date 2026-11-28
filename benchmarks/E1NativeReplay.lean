import CFDLean.Exec.Kernel

/-- Match the compiled one-step kernel to the separately replayed binary64 words, in cell order. -/
def main : IO Unit := do
  let bits := (CFDLean.Exec.eulerStepArray (3 : Float) 1 #[1, 2, 0]).map Float.toBits
  IO.println bits
  unless bits == #[0x3feaaaaaaaaaaaab, 0x3ff1555555555556, 0x3ff1555555555555] do
    throw (IO.userError "E1 binary64 replay mismatch")
