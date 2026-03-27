import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Ordering.Basic
import Mathlib.Order.Lattice

def Sequence (α: Type u) := ℕ -> α

namespace Sequence

def cons (a : α) (s : Sequence α) : Sequence α
  | 0 => a
  | i => s (i - 1)

def eq_by {a b : Sequence α} : (∀i, a i = b i ) ↔ a = b := by
  apply Iff.intro
  . intro h
    funext i
    exact h i
  . intro h i
    subst h
    rfl

def map₀ (a : α) : Sequence α := fun _ ↦ a

def map (f : α → β) (s : Sequence α) := fun i ↦ f (s i)

def map₂ (f : α → β → γ) (s : Sequence α) (t : Sequence β) := fun i ↦ f (s i) (t i)

abbrev const (a : α) := map₀ a

@[simp]
theorem map₀_def {a : α} : map₀ a n = a := rfl

@[simp]
theorem map_def (f : α → β) {s : Sequence α} : map f s i = f (s i) := rfl

@[simp]
theorem map₂_def (f : α → β → γ) {s : Sequence α} {t : Sequence β} : map₂ f s t i = f (s i) (t i) := rfl

end Sequence
