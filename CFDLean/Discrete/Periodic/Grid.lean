import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field

noncomputable section
namespace CFDLean.Periodic

open scoped BigOperators

structure Grid (I : Type*) where
  next : I ≃ I

namespace Grid

variable {I : Type*}

def prev (g : Grid I) : I → I := g.next.symm

theorem next_prev (g : Grid I) (i : I) : g.next (g.prev i) = i :=
  g.next.apply_symm_apply i

theorem prev_next (g : Grid I) (i : I) : g.prev (g.next i) = i :=
  g.next.symm_apply_apply i

theorem sum_prev [Fintype I] (g : Grid I) (f : I → ℝ) :
    ∑ i, f (g.prev i) = ∑ i, f i := by
  apply Fintype.sum_equiv g.next.symm
  intro i
  rfl

theorem sum_next [Fintype I] (g : Grid I) (f : I → ℝ) :
    ∑ i, f (g.next i) = ∑ i, f i := by
  apply Fintype.sum_equiv g.next
  intro i
  rfl

end Grid

def zmodGrid (N : ℕ) [NeZero N] : Grid (ZMod N) where
  next := Equiv.addRight 1

end CFDLean.Periodic
