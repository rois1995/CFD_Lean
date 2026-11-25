import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field

noncomputable section
namespace CFDLean.Burgers.Core

open scoped BigOperators

structure PeriodicGrid (I : Type*) where
  next : I ≃ I

namespace PeriodicGrid

variable {I : Type*}

def prev (g : PeriodicGrid I) : I → I := g.next.symm

theorem next_prev (g : PeriodicGrid I) (i : I) : g.next (g.prev i) = i :=
  g.next.apply_symm_apply i

theorem prev_next (g : PeriodicGrid I) (i : I) : g.prev (g.next i) = i :=
  g.next.symm_apply_apply i

theorem sum_prev [Fintype I] (g : PeriodicGrid I) (f : I → ℝ) :
    ∑ i, f (g.prev i) = ∑ i, f i := by
  apply Fintype.sum_equiv g.next.symm
  intro i
  rfl

theorem sum_next [Fintype I] (g : PeriodicGrid I) (f : I → ℝ) :
    ∑ i, f (g.next i) = ∑ i, f i := by
  apply Fintype.sum_equiv g.next
  intro i
  rfl

end PeriodicGrid

def zmodGrid (N : ℕ) [NeZero N] : PeriodicGrid (ZMod N) where
  next := Equiv.addRight 1

end CFDLean.Burgers.Core
