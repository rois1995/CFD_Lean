import CFDLean.Discrete.Periodic.NonuniformMuscl
import CFDLean.Schemes.Euler.FV1D

/-! FVN: the 1D Euler instance on a non-uniform periodic 1D mesh.

The states are encoded as `Vector 3` (density, momentum, energy), as in `CFDLean.Schemes.Euler.FV1D`. The first-order
step feeds the FV1D Rusanov face of the Euler flux into the reconstruction-independent update. The MUSCL face states
apply a scalar limiter to each encoded component (`componentwise`). This milestone states no Euler theorem on this
mesh; the FVN-E control (`CFDLean.Schemes.Euler.NonuniformControls`) checks these definitions on exact data. -/
noncomputable section
namespace CFDLean.Euler1D

open Periodic

variable {I : Type*}

/-- First-order Euler step on a non-uniform mesh with the FV1D Rusanov face. -/
def nonuniformStep (γ : ℝ) (m : Mesh1D I) (dt : ℝ) (U : I → Conservative 1) (i : I) : Conservative 1 :=
  decode (FV1D.Nonuniform.firstOrderStep m (FV1D.face (flux γ) (speed γ)) dt (fun j => encode (U j)) i)

/-- Left MUSCL state at face `i` (reconstructed in cell `i`) with the componentwise limiter `φ`. -/
def musclLeft (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (U : I → Conservative 1) (i : I) : Conservative 1 :=
  decode (FV1D.Nonuniform.leftState m (FV1D.Nonuniform.componentwise φ) (fun j => encode (U j)) i)

/-- Right MUSCL state at face `i` (reconstructed in cell `next i`) with the componentwise limiter `φ`. -/
def musclRight (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (U : I → Conservative 1) (i : I) : Conservative 1 :=
  decode (FV1D.Nonuniform.rightState m (FV1D.Nonuniform.componentwise φ) (fun j => encode (U j)) i)

end CFDLean.Euler1D
