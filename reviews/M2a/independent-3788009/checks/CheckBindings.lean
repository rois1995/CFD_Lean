import CFDLean

open CFDLean Coordinates PhysicalJacobian
open scoped Topology

example (U : Conservative 3) : decode (encode U) = U := decode_encode U
example (x : StateCoordinates) : encode (decode x) = x := encode_decode x
example (g : ℝ) : IsOpen {x : StateCoordinates | (decode x).Admissible g} := isOpen_admissible g

example (s : Vector 3) (hs : s ≠ 0) :
    dot (fun i => s i / Real.sqrt (squareSum s)) (fun i => s i / Real.sqrt (squareSum s)) = 1 :=
  unitNormal_dot_self s hs

example (g : ℝ) (U V : Conservative 3) (n : Vector 3) :
    let u : Vector 3 := fun i => U.momentum i / U.density
    let q := dot u n
    let b := dot V.momentum n - q * V.density
    let dp := (g - 1) * (V.energy - dot u V.momentum + squareSum u / 2 * V.density)
    jacobian g (encode U) n (encode V) = encode
      ⟨dot V.momentum n, fun i => q * V.momentum i + u i * b + dp * n i,
       q * (V.energy + dp) + ((U.energy + U.pressure g) / U.density) * b⟩ := by
  exact jacobian_action g U V n
