import CFDLean.Boundary.Stationary
import CFDLean.Geometry.MedianDual.Controls

noncomputable section
namespace CFDLean.Boundary.Controls
open Coordinates PhysicalJacobian Roe
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
attribute [local irreducible] Spectral.shift Spectral.b Spectral.dp Spectral.minus Spectral.plus Spectral.zero

private theorem sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
  simpa only [show (2 : ℝ)^2 = 4 by norm_num] using Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)

def axis : Vector 3 := ![1,0,0]
def moving (q p : ℝ) : Conservative 3 := ⟨1, ![q,0,0], p + q^2/2⟩

theorem moving_pressure (q p : ℝ) : (moving q p).pressure 2 = p := by
  norm_num [Conservative.pressure, moving, squareSum_three]

theorem moving_admissible (q p : ℝ) (hp : 0 < p) : (moving q p).Admissible 2 := by
  exact ⟨by norm_num [moving], by simpa only [moving_pressure] using hp⟩

theorem axis_ne : axis ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num [axis] at hh

theorem axis_unit : unitNormal axis = axis := by
  ext i
  fin_cases i <;> norm_num [unitNormal, area, squareSum_three, axis]

theorem moving_averageVelocity (q p r : ℝ) :
    averageVelocity (encode (moving q p)) (encode (moving q r)) = ![q,0,0] := by
  ext i
  fin_cases i <;> norm_num [averageVelocity, weight, root, velocity, encode, decode, moving]
  ring

theorem moving_enthalpy (q p r : ℝ) :
    averageEnthalpy 2 (encode (moving q p)) (encode (moving q r)) = p+r+q^2/2 := by
  norm_num [averageEnthalpy, weight, root, enthalpy, coordinatePressure, Conservative.pressure,
    encode, decode, moving, squareSum_three]
  ring

theorem moving_sound (q : ℝ) : soundSpeed 2 (encode (moving q 1)) (encode (moving q 3)) = 2 := by
  have hs : soundSquare 2 (encode (moving q 1)) (encode (moving q 3)) = 4 := by
    rw [soundSquare, moving_enthalpy, moving_averageVelocity]
    norm_num [squareSum_three]
  rw [soundSpeed, hs]
  exact sqrt_four

theorem moving_upwind_owner (q : ℝ) (hq : 2 ≤ q) :
    prescribedExteriorRoeTransfer 2 (moving q 1) (moving q 3) axis = encode (physicalFlux 2 (moving q 1) axis) := by
  apply prescribed_upwind_owner 2 _ _ _ (by norm_num) (moving_admissible _ _ (by norm_num))
    (moving_admissible _ _ (by norm_num)) axis_ne
  rw [moving_sound, moving_averageVelocity, axis_unit]
  simpa [dot_three, axis] using hq

theorem moving_upwind_exterior (q : ℝ) (hq : q ≤ -2) :
    prescribedExteriorRoeTransfer 2 (moving q 1) (moving q 3) axis = encode (physicalFlux 2 (moving q 3) axis) := by
  apply prescribed_upwind_exterior 2 _ _ _ (by norm_num) (moving_admissible _ _ (by norm_num))
    (moving_admissible _ _ (by norm_num)) axis_ne
  rw [moving_sound, moving_averageVelocity, axis_unit]
  simpa [dot_three, axis] using hq

theorem strict_outflow : prescribedExteriorRoeTransfer 2 (moving 3 1) (moving 3 3) axis = ![3,10,0,0,39/2] := by
  rw [moving_upwind_owner 3 (by norm_num)]
  ext i
  fin_cases i <;> norm_num [encode, physicalFlux, moving, Conservative.pressure, dot_three, squareSum_three, axis]

theorem strict_inflow : prescribedExteriorRoeTransfer 2 (moving (-3) 1) (moving (-3) 3) axis = ![-3,12,0,0,-63/2] := by
  rw [moving_upwind_exterior (-3) (by norm_num)]
  ext i
  fin_cases i <;> norm_num [encode, physicalFlux, moving, Conservative.pressure, dot_three, squareSum_three, axis]

theorem sonic_outflow : prescribedExteriorRoeTransfer 2 (moving 2 1) (moving 2 3) axis = ![2,5,0,0,8] := by
  rw [moving_upwind_owner 2 (by norm_num)]
  ext i
  fin_cases i <;> norm_num [encode, physicalFlux, moving, Conservative.pressure, dot_three, squareSum_three, axis]

theorem sonic_inflow : prescribedExteriorRoeTransfer 2 (moving (-2) 1) (moving (-2) 3) axis = ![-2,7,0,0,-16] := by
  rw [moving_upwind_exterior (-2) (by norm_num)]
  ext i
  fin_cases i <;> norm_num [encode, physicalFlux, moving, Conservative.pressure, dot_three, squareSum_three, axis]

theorem absolute_axis (v : StateCoordinates) :
    Spectral.absolute 2 0 4 axis 2 v = ![v 4 / 2, 2*v 1, 0, 0, 2*v 4] := by
  have hn : dot axis axis = 1 := by norm_num [dot_three, axis]
  have hc : (2 : ℝ)^2 = (2-1)*(4-squareSum (0 : Vector 3)/2) := by norm_num [squareSum_three]
  norm_num only [Spectral.absolute, Spectral.speed, Spectral.offset, dot_three, Pi.zero_apply,
    zero_mul, zero_add, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, abs_neg, abs_zero, zero_smul, add_zero,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [Spectral.minus_apply _ _ _ _ _ hn hc, Spectral.plus_apply _ _ _ _ _ hn hc]
  ext i
  fin_cases i <;> norm_num [Spectral.dp, Spectral.b, Spectral.acoustic, Spectral.vb, Spectral.vp,
    normalMomentum, projection, dot_three, squareSum_three, axis] <;> ring

def reflectedOwner : Conservative 3 := moving 1 (7/4)
def reflectedExterior : Conservative 3 := moving (-1) (7/4)

theorem reflected_averages :
    averageVelocity (encode reflectedOwner) (encode reflectedExterior) = 0 ∧
    averageEnthalpy 2 (encode reflectedOwner) (encode reflectedExterior) = 4 ∧
    soundSpeed 2 (encode reflectedOwner) (encode reflectedExterior) = 2 := by
  have hu : averageVelocity (encode reflectedOwner) (encode reflectedExterior) = 0 := by
    ext i
    fin_cases i <;> norm_num [averageVelocity, weight, root, velocity, encode, decode, reflectedOwner, reflectedExterior, moving]
  have hh : averageEnthalpy 2 (encode reflectedOwner) (encode reflectedExterior) = 4 := by
    norm_num [averageEnthalpy, weight, root, enthalpy, coordinatePressure, Conservative.pressure,
      encode, decode, reflectedOwner, reflectedExterior, moving, squareSum_three]
  have hc : soundSpeed 2 (encode reflectedOwner) (encode reflectedExterior) = 2 := by
    norm_num [soundSpeed, soundSquare, hu, hh, squareSum_three]
    exact sqrt_four
  exact ⟨hu, hh, hc⟩

theorem reflected_roe : prescribedExteriorRoeTransfer 2 reflectedOwner reflectedExterior axis = ![0,19/4,0,0,0] := by
  have hd : Spectral.dissipation 2 (encode reflectedOwner) (encode reflectedExterior) (unitNormal axis)
      (encode reflectedExterior - encode reflectedOwner) = ![0,-4,0,0,0] := by
    unfold Spectral.dissipation
    rw [reflected_averages.1, reflected_averages.2.1, reflected_averages.2.2, axis_unit, absolute_axis]
    ext i
    fin_cases i <;> norm_num [encode, reflectedOwner, reflectedExterior, moving]
  simp only [prescribedExteriorRoeTransfer, numericalFlux, encode_decode]
  rw [roeFluxCoordinates, if_neg axis_ne, hd]
  ext i
  fin_cases i <;> norm_num [coordinateFlux, encode, physicalFlux, decode, reflectedOwner, reflectedExterior,
    moving, Conservative.pressure, dot_three, squareSum_three, area, axis]

theorem reflected_not_wall : prescribedExteriorRoeTransfer 2 reflectedOwner reflectedExterior axis ≠ wallTransfer 2 reflectedOwner axis := by
  rw [reflected_roe]
  intro h
  have hh := congrFun h 1
  norm_num [wallTransfer, pressureTransfer, reflectedOwner, moving_pressure, axis] at hh

theorem mismatching_exterior : prescribedExteriorRoeTransfer 2 (moving 0 1) (moving 0 3) axis = ![-1/2,2,0,0,-2] := by
  have hh : averageEnthalpy 2 (encode (moving 0 1)) (encode (moving 0 3)) = 4 := by
    rw [moving_enthalpy]; norm_num
  have hu : averageVelocity (encode (moving 0 1)) (encode (moving 0 3)) = 0 := by
    rw [moving_averageVelocity]
    ext i
    fin_cases i <;> rfl
  have hd : Spectral.dissipation 2 (encode (moving 0 1)) (encode (moving 0 3)) (unitNormal axis)
      (encode (moving 0 3)-encode (moving 0 1)) = ![1,0,0,0,4] := by
    unfold Spectral.dissipation
    rw [hu, hh, moving_sound, axis_unit, absolute_axis]
    ext i
    fin_cases i <;> norm_num [encode, moving]
  simp only [prescribedExteriorRoeTransfer, numericalFlux, encode_decode]
  rw [roeFluxCoordinates, if_neg axis_ne, hd]
  ext i
  fin_cases i <;> norm_num [coordinateFlux, encode, physicalFlux, decode, moving,
    Conservative.pressure, dot_three, squareSum_three, area, axis]

abbrev standard := MedianDual.Controls.standard
abbrev wallPatch : standard.Boundary := MedianDual.Controls.standardBoundary
def openPatch : standard.Boundary := ⟨((0,1),0), by decide⟩
def mixedKinds (F : Finset (Fin 4)) : Kind :=
  if F = primalFace standard wallPatch then .slipWall else .prescribedExteriorRoe

theorem mixed_corner : standard.interfaces.owner wallPatch = standard.interfaces.owner openPatch ∧
    patchKind standard mixedKinds wallPatch = .slipWall ∧
    patchKind standard mixedKinds openPatch = .prescribedExteriorRoe := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [patchKind, mixedKinds]
  · have hf : primalFace standard openPatch ≠ primalFace standard wallPatch := by decide
    simp [patchKind, mixedKinds, hf]

theorem wall_patch_transfer : patchTransfer standard 2 mixedKinds (fun _ => moving 0 1)
    (fun _ => moving 0 1) wallPatch = ![0,0,0,-1/6,0] := by
  rw [patchTransfer_wall standard 2 mixedKinds _ _ wallPatch mixed_corner.2.1]
  ext i
  fin_cases i <;> norm_num [wallTransfer, pressureTransfer, moving_pressure, MedianDual.MeshData.boundaryArea,
    MedianDual.MeshData.faceArea, MedianDual.MeshData.points, MedianDual.Controls.standard,
    MedianDual.Controls.oneCell, MedianDual.Controls.standardBoundary, MedianDual.Controls.standardPoints,
    MedianDual.faceVector, MedianDual.triangle, MedianDual.cross]

theorem open_patch_transfer : patchTransfer standard 2 mixedKinds (fun _ => moving 0 1)
    (fun _ => moving 0 1) openPatch = ![0,-1/6,0,0,0] := by
  rw [patchTransfer_prescribed standard 2 mixedKinds _ _ openPatch mixed_corner.2.2]
  change prescribedExteriorRoeTransfer 2 (moving 0 1) (moving 0 1) _ = _
  rw [prescribed_consistency]
  ext i
  fin_cases i <;> norm_num [encode, physicalFlux, moving, Conservative.pressure, squareSum_three, dot_three,
    MedianDual.MeshData.boundaryArea, MedianDual.MeshData.faceArea, MedianDual.MeshData.points,
    MedianDual.Controls.standard, MedianDual.Controls.oneCell, MedianDual.Controls.standardPoints, openPatch,
    MedianDual.faceVector, MedianDual.triangle, MedianDual.cross]

def obliqueOwner : Conservative 3 := ⟨2, ![8,-6,2], 29⟩
def obliqueArea : Vector 3 := ![3,4,0]

theorem oblique_admissible : obliqueOwner.Admissible 2 := by
  norm_num [Conservative.Admissible, Conservative.pressure, obliqueOwner, squareSum_three]

theorem oblique_traction : wallTransfer 2 obliqueOwner obliqueArea = ![0,9,12,0,0] := by
  ext i
  fin_cases i <;> norm_num [wallTransfer, pressureTransfer, Conservative.pressure, obliqueOwner, obliqueArea, squareSum_three]

theorem oblique_physical : wallTransfer 2 obliqueOwner obliqueArea = encode (physicalFlux 2 obliqueOwner obliqueArea) := by
  apply (wall_eq_physical_iff _ _ _).mpr
  norm_num [obliqueOwner, obliqueArea, dot_three]

theorem normal_flow_incompatible : wallTransfer 2 (moving 1 1) axis ≠ encode (physicalFlux 2 (moving 1 1) axis) := by
  intro h
  have hn := (wall_eq_physical_iff _ _ _).mp h
  norm_num [moving, axis, dot_three] at hn

theorem owner_sampling_differs : wallTransfer 2 (moving 0 1) axis ≠
    pressureTransfer ((6*(moving 0 1).pressure 2+(moving 0 2).pressure 2+(moving 0 4).pressure 2)/8) axis := by
  intro h
  have hh := congrFun h 1
  norm_num [wallTransfer, pressureTransfer, moving_pressure, axis] at hh

end CFDLean.Boundary.Controls
