import Mathlib.Data.Int.Init
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Int.Parity

import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Defs

import Mathlib.Algebra.Ring.Parity -- Odd numbers
import Mathlib.Algebra.Group.Even -- Even numbers


namespace Q1

abbrev S p q := ((¬p) → q) → (p → (¬q))

/-
Show that `S` is not a tautology nor a contradiction
-/
#eval S True True -- => False
#eval S True False -- => True
#eval S False True -- => True
#eval S False False -- => True

/-
Show that given `p = False` and `S = True`,
`q = True ∨ q = False`
-/
#eval S False True -- => True
#eval S False False -- => True

abbrev S' p q := ¬S p q

example p q : S' p q ↔ (p ∧ q) := by grind

/-
Write a minimal statement T that is logically equivalent to `¬S`
-/
abbrev T p q := p ∧ q

end Q1

namespace Q2

abbrev p x y  := Rat.isInt (x * y)

example : ∀x : ℚ, ∃y : ℚ, p x y := by
  intro x

  by_cases h_x : x = 0
  case pos =>
    exists 0
    simp [p]
    decide

  case neg =>
    exists x⁻¹
    unfold p
    rw [Rat.mul_inv_cancel x h_x]
    decide

example : ¬(∃y : ℚ, y ≠ 0 ∧ (∀x : ℚ, p x y)) := by
  simp
  intro y y_neq_0
  let x := y⁻¹/2
  exists x
  simp [p, x, Rat.isInt, Rat.div_def, Rat.mul_comm,
        <-Rat.mul_assoc, Rat.mul_inv_cancel y y_neq_0]

example : ¬(∀x y z : ℚ, p x y → p y z → p x z) := by
  simp_all
  exists 1/2, 2
  apply And.intro
  . simp [p, Rat.div_def, Rat.inv_mul_cancel]; decide

  exists 1
  apply And.intro
  . simp [p]; decide;
  simp [p, Rat.isInt, Rat.div_def]

end Q2

namespace Q3

example (x : ℤ) : Odd (x^2 + 4*x + 7) ↔ Even x := by
  by_cases Even x
  case pos even_x =>
    let ⟨k, h_k⟩ := even_x
    rw [show Even x = True by exact eq_true even_x]
    simp
    exists (2 * k^2 + 4*k + 3)
    grind

  case neg not_even_x =>
    let ⟨k, h_k⟩ := Int.not_even_iff_odd.mp not_even_x
    rw [show Even x = False by exact eq_false not_even_x]
    simp
    exists 2*k^2 + 6*k + 6
    grind

end Q3

namespace Q4

abbrev S (a b : ℤ) (_a_gt_b : a > b := by grind) (_b_ge_0 : b ≥ 0 := by grind) := ∃x k : ℤ, x^2 = a * k + b
abbrev S' := S 4 3

example : ¬S' ↔ ∀x k : ℤ, x^2 ≠ 4*k + 3 := by grind

example : ¬S' := by
  simp
  intro x k
  have odd : Odd (4 * k + 3) := by grind

  by_cases Even x

  case pos even_x =>
    have even_x_sq : Even (x^2) := by grind
    intro x_sq_eq_odd
    have odd_x : Odd (x^2) := x_sq_eq_odd ▸ odd
    grind

  case neg not_even_x =>
    have odd_x : Odd x := by grind
    let ⟨m, h_m⟩ := odd_x
    subst h_m
    simp [add_sq, mul_pow, <-mul_assoc]
    grind

/-
Find one pair (a, b) such that S(a, b) is False
-/
example : ¬S 8 7 := by
  simp
  intro x k
  have odd : Odd (8 * k + 7) := by grind

  by_cases Even x
  case pos even_x =>
    have even_x_sq : Even (x^2) := by grind
    grind
  case neg not_even_x =>
    have odd_x : Odd x := by grind
    let ⟨m, h_m⟩ := odd_x
    subst h_m
    grind

/-
Find one pair (a, b) such that S(a, b) is True
-/
example : S 1 0 := by simp [S]

end Q4
