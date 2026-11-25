import CFDLean.Geometry.MeshBoundary
import CFDLean.Papers.JST1.Euler.IsmailRoe
import CFDLean.Papers.JST1.Viscous.Wall
import CFDLean.Papers.JST1.Viscous.Flux

/-! The complete semi-discrete scheme of paper 1 (`def:scheme`, lines 126-140) on a weighted simplex mesh (a simplex
mesh, or the averaged operator of a mixed mesh): Ismail-Roe central flux on `n_ik`, scalar dissipation, hybridized
boundary closure at face points, P1 Galerkin viscous operator with `K(w̄_T)`, weak wall per element. The residual is
the contribution to `V_i du_i/dt`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1
namespace Scheme

structure Data (ι C Q : Type) (d : ℕ) where
  M : WMesh ι C d
  g : Gas
  /-- Scalar dissipation: coefficient `λ_ik`, `ε2_ik`, `ε4_ik`, Laplacian neighbours `N*(i)`. -/
  lam : ι → ι → ℝ
  eps2 : ι → ι → ℝ
  eps4 : ι → ι → ℝ
  Nstar : ι → Finset ι
  /-- Boundary closure: basis values `φ_qk`, scaled normals `N_q`, projected states `ũ_q`, boundary fluxes `F*_q`. -/
  φ : Q → ι → ℝ
  N : Q → Vec d
  ut : Q → State d
  Fs : Q → State d
  /-- Viscous parameters per cell (`μ + μ_t`, `κ`, `R`). -/
  Pv : C → ViscParams
  /-- Weak wall: projector, data, wall faces (opposite local vertex) of each cell, penalty constant. -/
  P : Matrix (Channel d) (Channel d) ℝ
  gw : State d
  walls : C → Finset (Fin (d + 1))
  c : ℝ

variable {ι C Q : Type} [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype Q] {d : ℕ} (S : Data ι C Q d)
  (u : ι → State d)

def w (i : ι) : State d := entropyVars S.g (u i)
def ut' (i : ι) : State d := enthalpyState S.g (u i)
def L (i : ι) : State d := ∑ k ∈ S.Nstar i, (ut' S u k - ut' S u i)

def central (i k : ι) : State d := ismailRoe S.g (u i) (u k) (S.M.n i k)
def diss2 (i k : ι) : State d := (S.lam i k * S.eps2 i k) • (ut' S u i - ut' S u k)
def diss4 (i k : ι) : State d := (S.lam i k * S.eps4 i k) • (L S u i - L S u k)

def closure (i : ι) : State d :=
  ∑ q, S.φ q i • (ismailRoe S.g (u i) (S.ut q) (S.N q) - ∑ k, S.φ q k • ismailRoe S.g (S.ut q) (u k) (S.N q) + S.Fs q)

def wloc (T : C) (a : Fin (d + 1)) : State d := w S u (S.M.vert T a)
def wbar (T : C) : State d := (1 / ((d : ℝ) + 1)) • ∑ a, wloc S u T a
def K (T : C) : Matrix (Channel d) (Fin d) ℝ → Matrix (Channel d) (Fin d) ℝ := viscFlux (S.Pv T) (wbar S u T)

def visc (i : ι) : State d := S.M.galerkinRes (fun T => K S u T (S.M.gradW (w S u) T)) i

def wall (i : ι) : State d :=
  ∑ T, ∑ a, if S.M.vert T a = i then
    S.M.ω T • Wall.Rwall (S.M.simplex T) (K S u T) S.P S.gw (S.walls T) S.c (wloc S u T) a else 0

/-- Contribution to `V_i du_i/dt`. -/
def resid (i : ι) : State d :=
  -(∑ k, (central S u i k + diss2 S u i k - diss4 S u i k)) - closure S u i + visc S u i + wall S u i

/-! Terms of the entropy balance. -/

def Bterm : ℝ := ∑ q, (Num.dot (fluxPot (S.ut q)) (S.N q) - pairF (entropyVars S.g (S.ut q)) (S.Fs q))
def Pi2 : ℝ := (1 / 2) * ∑ i, ∑ k, pairF (w S u k - w S u i) (diss2 S u i k)
def Pi4 : ℝ := -((1 / 2) * ∑ i, ∑ k, pairF (w S u k - w S u i) (diss4 S u i k))
def Dg (T : C) : ℝ := Wall.Dgal (S.M.simplex T) (K S u T) (wloc S u T)
def Pw (T : C) : ℝ := Wall.PiW (S.M.simplex T) (K S u T) S.P S.gw (S.walls T) S.c (wloc S u T)
def wallFlux : ℝ :=
  ∑ T, S.M.ω T * ∑ o ∈ S.walls T, Wall.area (S.M.simplex T) o / d *
    ∑ a ∈ Finset.univ.erase o,
      pairF S.gw (Wall.Fhat (S.M.simplex T) (K S u T) S.P S.gw (S.walls T) S.c (wloc S u T) o a)

end Scheme
end CFDLean.JST1
