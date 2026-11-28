import CFDLean.Discrete.Periodic.MusclReconstruction
import CFDLean.Discrete.Periodic.Weno
import CFDLean.Discrete.Periodic.Muscl

namespace ReviewCases.Reconstruction

open CFDLean CFDLean.Periodic CFDLean.FV1D.Reconstruction

private def grid : Grid (Fin 6) := ⟨Equiv.addRight 1⟩
private def means : Fin 6 → ℚ := ![1, 2, 4, 3, 1, 0]

-- Independently fitting the three quadratics to the means gives candidate values (-1,1,3)/6
-- and (5,3,1)/6 at the seam. Their integrated derivative-square indicators are
-- (4/3,13/3,1) and (4/3,1,25/3), respectively.
example : (wenoJS5 grid 1 one_pos ⟨(1 : ℚ), one_pos⟩).traces means 5 = (1587/4786, 475/898) := by
  decide +kernel

-- The same seam through the accepted minmod reconstruction has slopes 0 and 1.
example : (muscl (Mesh1D.uniform grid 1 one_pos) Scalar.FiniteVolume.minmod).traces
    (fun i => (means i : ℝ)) 5 = (0, 1/2) := by
  change (0 + (1/2 : ℝ) • Scalar.FiniteVolume.minmod ((1 / ((1+1)/2) : ℝ) • (0-1))
      ((1 / ((1+1)/2) : ℝ) • (1-0)),
    1 - (1/2 : ℝ) • Scalar.FiniteVolume.minmod ((1 / ((1+1)/2) : ℝ) • (1-0))
      ((1 / ((1+1)/2) : ℝ) • (2-1))) = _
  norm_num [Scalar.FiniteVolume.minmod]

end ReviewCases.Reconstruction
