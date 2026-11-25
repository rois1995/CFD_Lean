import CFDLean.Geometry.Simplex

/-! Weak wall closure on one simplex (paper appendix, proof of `thm:wall`, lines 1067-1090). Generic in the
component type `κ`, the frozen viscous map `K` on gradients and the constant projector `P`. The adjoint factor
is `ς = 1`. Wall faces are given by their opposite local vertex `o ∈ walls`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1
namespace Wall
variable {κ : Type} [Fintype κ] {d : ℕ}

/-- `e ⊗ N`. -/
def outerK (e : κ → ℝ) (N : Vec d) : Matrix κ (Fin d) ℝ := fun r α => e r * N α

/-- Element gradient `G_T = Σ_a w_a ⊗ g_a`. -/
def gradT (T : Simplex d) (w : Fin (d + 1) → κ → ℝ) : Matrix κ (Fin d) ℝ :=
  ∑ a, outerK (w a) (T.grad a)

/-- Area `A_f = d |T| |g_o|`, unit outward normal `N_f = -g_o/|g_o|`, height `h_f = d|T|/A_f` of the face
opposite `o` (so `A_f N_f = T.facet o`). -/
def area (T : Simplex d) (o : Fin (d + 1)) : ℝ := d * T.vol * len (T.grad o)
def normal (T : Simplex d) (o : Fin (d + 1)) : Vec d := (-(1 / len (T.grad o))) • T.grad o
def hf (T : Simplex d) (o : Fin (d + 1)) : ℝ := d * T.vol / area T o

/-- Penalty `σ_f = c N_T d / h_f`. -/
def sigmaF (T : Simplex d) (walls : Finset (Fin (d + 1))) (c : ℝ) (o : Fin (d + 1)) : ℝ :=
  c * walls.card * d / hf T o

/-- `e_a = P (w_a - g)`. -/
def eW (P : Matrix κ κ ℝ) (gw : κ → ℝ) (w : Fin (d + 1) → κ → ℝ) (a : Fin (d + 1)) : κ → ℝ :=
  P.mulVec (w a - gw)

/-- Galerkin dissipation `D^gal_T = |T| G : K G`. -/
def Dgal (T : Simplex d) (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ) (w : Fin (d + 1) → κ → ℝ) : ℝ :=
  T.vol * frob (gradT T w) (K (gradT T w))

/-- `X_f = (A_f/d) Σ_{a∈f} |e_a ⊗ N_f|²_K`. -/
def Xf (T : Simplex d) (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ) (P : Matrix κ κ ℝ) (gw : κ → ℝ)
    (w : Fin (d + 1) → κ → ℝ) (o : Fin (d + 1)) : ℝ :=
  area T o / d * ∑ a ∈ Finset.univ.erase o,
    frob (outerK (eW P gw w a) (normal T o)) (K (outerK (eW P gw w a) (normal T o)))

/-- Wall production `Π^w_T = Σ_f [(1+ς)(A_f/d) Σ_{a∈f} e_a · F_T N_f - σ_f X_f]`, `ς = 1`. -/
def PiW (T : Simplex d) (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ) (P : Matrix κ κ ℝ) (gw : κ → ℝ)
    (walls : Finset (Fin (d + 1))) (c : ℝ) (w : Fin (d + 1) → κ → ℝ) : ℝ :=
  ∑ o ∈ walls, (2 * (area T o / d) * ∑ a ∈ Finset.univ.erase o,
      pairF (eW P gw w a) ((K (gradT T w)).mulVec (normal T o)) -
    sigmaF T walls c o * Xf T K P gw w o)

/-- Consistency and penalty flux at a node of a wall face: `F̂_a = P F_T N_f - σ_f M_f e_a`,
`M_f e = P (K (P e ⊗ N_f)) N_f`. -/
def Fhat (T : Simplex d) (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ) (P : Matrix κ κ ℝ) (gw : κ → ℝ)
    (walls : Finset (Fin (d + 1))) (c : ℝ) (w : Fin (d + 1) → κ → ℝ) (o a : Fin (d + 1)) : κ → ℝ :=
  P.mulVec ((K (gradT T w)).mulVec (normal T o)) -
    sigmaF T walls c o • P.mulVec ((K (outerK (P.mulVec (eW P gw w a)) (normal T o))).mulVec (normal T o))

/-- Wall residual of node `b` (added to `V_b du_b/dt`): `(A_f/d) F̂_b` on every wall face that contains `b`, plus
the symmetric adjoint term `(K E_f) g_b`, `E_f = (A_f/d) Σ_{a∈f} e_a ⊗ N_f` (its `w`-pairing is
`(A_f/d) Σ_a e_a · F_T N_f`, and it sums to zero over the nodes of `T`). -/
def Rwall (T : Simplex d) (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ) (P : Matrix κ κ ℝ) (gw : κ → ℝ)
    (walls : Finset (Fin (d + 1))) (c : ℝ) (w : Fin (d + 1) → κ → ℝ) (b : Fin (d + 1)) : κ → ℝ :=
  ∑ o ∈ walls, ((if b ≠ o then (area T o / d) • Fhat T K P gw walls c w o b else 0) +
    (K ((area T o / d) • ∑ a ∈ Finset.univ.erase o, outerK (eW P gw w a) (normal T o))).mulVec (T.grad b))

/-- Galerkin viscous residual of node `b`: `-|T| (K G_T) g_b`. -/
def Rvisc (T : Simplex d) (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ) (w : Fin (d + 1) → κ → ℝ)
    (b : Fin (d + 1)) : κ → ℝ :=
  -(T.vol • (K (gradT T w)).mulVec (T.grad b))

end Wall
end CFDLean.JST1
