import CFDLean.Geometry.MedianDual

noncomputable section
namespace CFDLean.Boundary
open Coordinates
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

/-- These names distinguish the selected algorithms from other wall/farfield variants. -/
inductive Kind where
  | slipWall
  | inviscidSymmetryTraction
  | prescribedExteriorRoe
  deriving DecidableEq

def pressureTransfer (p : ℝ) (T : Vector 3) : StateCoordinates :=
  ![0, p * T 0, p * T 1, p * T 2, 0]

def wallTransfer (γ : ℝ) (U : Conservative 3) (T : Vector 3) : StateCoordinates :=
  pressureTransfer (U.pressure γ) T

/-- Interior owner is left, prescribed exterior is right; T is already integrated outward area. -/
def prescribedExteriorRoeTransfer (γ : ℝ) (U V : Conservative 3) (T : Vector 3) : StateCoordinates :=
  encode (Roe.numericalFlux γ U V T)

def transfer (γ : ℝ) (k : Kind) (U V : Conservative 3) (T : Vector 3) : StateCoordinates :=
  match k with
  | .slipWall | .inviscidSymmetryTraction => wallTransfer γ U T
  | .prescribedExteriorRoe => prescribedExteriorRoeTransfer γ U V T

theorem wall_mass (γ : ℝ) (U : Conservative 3) (T : Vector 3) : wallTransfer γ U T 0 = 0 := rfl

theorem wall_energy (γ : ℝ) (U : Conservative 3) (T : Vector 3) : wallTransfer γ U T 4 = 0 := rfl

theorem wall_momentum (γ : ℝ) (U : Conservative 3) (T : Vector 3) (i : Fin 3) :
    (decode (wallTransfer γ U T)).momentum i = U.pressure γ * T i := by
  fin_cases i <;> rfl

theorem wall_zero (γ : ℝ) (U : Conservative 3) : wallTransfer γ U 0 = 0 := by
  ext i
  fin_cases i <;> simp [wallTransfer, pressureTransfer]

theorem wall_add (γ : ℝ) (U : Conservative 3) (S T : Vector 3) :
    wallTransfer γ U (S + T) = wallTransfer γ U S + wallTransfer γ U T := by
  ext i
  fin_cases i <;> simp [wallTransfer, pressureTransfer, mul_add]

theorem wall_smul (γ a : ℝ) (U : Conservative 3) (T : Vector 3) :
    wallTransfer γ U (a • T) = a • wallTransfer γ U T := by
  ext i
  fin_cases i <;> simp [wallTransfer, pressureTransfer, mul_left_comm]

theorem wall_reverse (γ : ℝ) (U : Conservative 3) (T : Vector 3) :
    wallTransfer γ U (-T) = -wallTransfer γ U T := by
  ext i
  fin_cases i <;> simp [wallTransfer, pressureTransfer]

theorem wall_pressure_pos (γ : ℝ) (U : Conservative 3) (hU : U.Admissible γ) : 0 < U.pressure γ := hU.2

theorem wall_eq_physical_iff (γ : ℝ) (U : Conservative 3) (T : Vector 3) :
    wallTransfer γ U T = encode (physicalFlux γ U T) ↔ dot U.momentum T = 0 := by
  constructor
  · intro h
    exact (congrFun h 0).symm
  · intro h
    ext i
    fin_cases i <;> simp [wallTransfer, pressureTransfer, physicalFlux, encode, h]

/-- A physical velocity/unit-normal interpretation needs positive density and a nonzero patch. -/
theorem wall_eq_physical_iff_normalVelocity (γ : ℝ) (U : Conservative 3) (T : Vector 3)
    (hρ : 0 < U.density) (hT : T ≠ 0) :
    wallTransfer γ U T = encode (physicalFlux γ U T) ↔
      dot (fun i => U.momentum i / U.density) (unitNormal T) = 0 := by
  have hA := ne_of_gt (area_pos T hT)
  have hv : dot (fun i => U.momentum i / U.density) (unitNormal T) =
      dot U.momentum T / (U.density * area T) := by
    simp only [dot_three, unitNormal]
    field_simp [ne_of_gt hρ, hA]
  rw [wall_eq_physical_iff, hv]
  simp [ne_of_gt hρ, hA]

theorem prescribed_consistency (γ : ℝ) (U : Conservative 3) (T : Vector 3) :
    prescribedExteriorRoeTransfer γ U U T = encode (physicalFlux γ U T) := by
  rw [prescribedExteriorRoeTransfer, Roe.numericalFlux_consistency]

theorem prescribed_zero (γ : ℝ) (U V : Conservative 3) : prescribedExteriorRoeTransfer γ U V 0 = 0 := by
  rw [prescribedExteriorRoeTransfer, Roe.numericalFlux_zero]
  ext i
  fin_cases i <;> rfl

theorem prescribed_scale (γ a : ℝ) (U V : Conservative 3) (T : Vector 3) (ha : 0 ≤ a) :
    prescribedExteriorRoeTransfer γ U V (a • T) = a • prescribedExteriorRoeTransfer γ U V T := by
  simp only [prescribedExteriorRoeTransfer, Roe.numericalFlux, encode_decode]
  exact Roe.roeFluxCoordinates_scale γ a (encode U) (encode V) T ha

theorem prescribed_reverse (γ : ℝ) (U V : Conservative 3) (T : Vector 3) :
    prescribedExteriorRoeTransfer γ V U (-T) = -prescribedExteriorRoeTransfer γ U V T :=
  Assembly.encoded_reverse γ U V T

theorem prescribed_upwind_owner (γ : ℝ) (U V : Conservative 3) (T : Vector 3)
    (hγ : 1 < γ) (hU : U.Admissible γ) (hV : V.Admissible γ) (hT : T ≠ 0)
    (hup : Roe.soundSpeed γ (encode U) (encode V) ≤
      dot (Roe.averageVelocity (encode U) (encode V)) (unitNormal T)) :
    prescribedExteriorRoeTransfer γ U V T = encode (physicalFlux γ U T) := by
  rw [prescribedExteriorRoeTransfer, Roe.numericalFlux_upwind_left γ U V T hγ hU hV hT hup]

theorem prescribed_upwind_exterior (γ : ℝ) (U V : Conservative 3) (T : Vector 3)
    (hγ : 1 < γ) (hU : U.Admissible γ) (hV : V.Admissible γ) (hT : T ≠ 0)
    (hup : dot (Roe.averageVelocity (encode U) (encode V)) (unitNormal T) ≤
      -Roe.soundSpeed γ (encode U) (encode V)) :
    prescribedExteriorRoeTransfer γ U V T = encode (physicalFlux γ V T) := by
  rw [prescribedExteriorRoeTransfer, Roe.numericalFlux_upwind_right γ U V T hγ hU hV hT hup]

def primalFace {n m : ℕ} (M : MedianDual.MeshData n m) (b : M.Boundary) : Finset (Fin n) :=
  M.faceID b.1.1

def patchKind {n m : ℕ} (M : MedianDual.MeshData n m) (k : Finset (Fin n) → Kind) (b : M.Boundary) : Kind :=
  k (primalFace M b)

def patchExterior {n m : ℕ} (M : MedianDual.MeshData n m)
    (V : Finset (Fin n) → Conservative 3) (b : M.Boundary) : Conservative 3 := V (primalFace M b)

def patchTransfer {n m : ℕ} (M : MedianDual.MeshData n m) (γ : ℝ)
    (k : Finset (Fin n) → Kind) (V : Finset (Fin n) → Conservative 3)
    (U : Fin n → Conservative 3) (b : M.Boundary) : StateCoordinates :=
  transfer γ (patchKind M k b) (U (M.interfaces.owner b)) (patchExterior M V b) (M.boundaryArea b)

theorem boundary_record_unique {n m : ℕ} (M : MedianDual.MeshData n m) (b c : M.Boundary)
    (hf : primalFace M b = primalFace M c) (hi : M.interfaces.owner b = M.interfaces.owner c) : b = c :=
  M.boundaryKey_injective (Prod.ext hf hi)

theorem boundary_record_range {n m : ℕ} (M : MedianDual.MeshData n m) (F : Finset (Fin n)) (i : Fin n) :
    (∃ b : M.Boundary, primalFace M b = F ∧ M.interfaces.owner b = i) ↔ M.faceCount F = 1 ∧ i ∈ F := by
  simpa only [MedianDual.MeshData.boundaryKey, primalFace, MedianDual.MeshData.interfaces, Prod.mk.injEq] using
    M.boundaryKey_range F i

theorem patchKind_coherent {n m : ℕ} (M : MedianDual.MeshData n m) (k : Finset (Fin n) → Kind)
    (b c : M.Boundary) (h : primalFace M b = primalFace M c) : patchKind M k b = patchKind M k c := by
  simp only [patchKind, h]

theorem patchExterior_coherent {n m : ℕ} (M : MedianDual.MeshData n m)
    (V : Finset (Fin n) → Conservative 3) (b c : M.Boundary) (h : primalFace M b = primalFace M c) :
    patchExterior M V b = patchExterior M V c := by
  simp only [patchExterior, h]

theorem patchTransfer_wall {n m : ℕ} (M : MedianDual.MeshData n m) (γ : ℝ)
    (k : Finset (Fin n) → Kind) (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3)
    (b : M.Boundary) (h : patchKind M k b = .slipWall) :
    patchTransfer M γ k V U b = wallTransfer γ (U (M.interfaces.owner b)) (M.boundaryArea b) := by
  simp only [patchTransfer, h, transfer]

theorem patchTransfer_symmetry {n m : ℕ} (M : MedianDual.MeshData n m) (γ : ℝ)
    (k : Finset (Fin n) → Kind) (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3)
    (b : M.Boundary) (h : patchKind M k b = .inviscidSymmetryTraction) :
    patchTransfer M γ k V U b = wallTransfer γ (U (M.interfaces.owner b)) (M.boundaryArea b) := by
  simp only [patchTransfer, h, transfer]

theorem patchTransfer_prescribed {n m : ℕ} (M : MedianDual.MeshData n m) (γ : ℝ)
    (k : Finset (Fin n) → Kind) (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3)
    (b : M.Boundary) (h : patchKind M k b = .prescribedExteriorRoe) :
    patchTransfer M γ k V U b = prescribedExteriorRoeTransfer γ (U (M.interfaces.owner b))
      (patchExterior M V b) (M.boundaryArea b) := by
  simp only [patchTransfer, h, transfer]

end CFDLean.Boundary
