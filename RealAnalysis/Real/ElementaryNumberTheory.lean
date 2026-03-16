
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

def odd (n : ℤ) := ∃k : ℤ, n = 2*k + 1
def even (n : ℤ) := ∃k : ℤ, n = 2 * k

-- a|b
def divides (a b : ℤ) := ∃k : ℤ, k * a = b

namespace divides

def all : ∀a : ℤ, divides a a := by
  intro a
  rw [divides]
  exists 1
  exact Int.one_mul _

end divides

def prime (n : ℤ) := ∀k > 1, k < n → ¬ divides k n

example : ∀x : ℤ, even x → even (x^2) := by
  intro x
  simp [even]
  intro k x_even
  exists 2 * k^2
  subst x_even
  grind_linarith
