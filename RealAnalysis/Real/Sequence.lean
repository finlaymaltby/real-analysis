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



-- instance [Add α] : Add (Sequence α) where
--     add (s₁ s₂ : Sequence α) := λ n ↦ s₁ n + s₂ n

-- instance [Zero α] : Zero (Sequence α) where
--     zero := const 0

-- instance [Neg α] : Neg (Sequence α) where
--     neg (s₁ : Sequence α) := λ n ↦ -s₁ n

-- instance [Mul α] : Mul (Sequence α) where
--     mul (s₁ s₂ : Sequence α) := λ n ↦ (s₁ n) * (s₂ n)

-- instance [One α] : One (Sequence α) where
--     one := const 1

-- instance [Inv α] : Inv (Sequence α) where
--     inv s := λ n ↦ Inv.inv (s n)

-- instance [HMul α β β] : SMul α (Sequence β) where
--     smul m s := λ n ↦ m * s n

-- instance : CommRing (Sequence ℚ) where
--     add_assoc s t u := by
--         rw [← @Add.add_eq_hAdd, Add.add, instAdd]
--         simp!
--         funext n
--         exact Rat.add_assoc _ _ _

--     zero_add s := by
--         rw [← @Add.add_eq_hAdd, Add.add, instAdd]
--         simp!
--         funext n
--         exact add_eq_right.mpr rfl

--     add_zero s := by
--         rw [← @Add.add_eq_hAdd, Add.add, instAdd]
--         simp!
--         funext n
--         exact add_eq_left.mpr rfl

--     nsmul a s := λ n ↦ a * s n

--     nsmul_zero s := by
--         rw [@Rat.natCast_ofNat]
--         rw (occs := .pos [2]) [OfNat.ofNat]
--         rw [Zero.toOfNat0, Zero.zero, instZero]
--         simp

--     nsmul_succ a s := by
--         let t : Sequence ℚ := fun n => ↑a * s n
--         rw [show t + s = (fun n => ↑a * s n + s n) by
--             exact (congrArg (HAdd.hAdd t) ∘ fun a => a) rfl
--         ]
--         funext n
--         rw [Rat.natCast_add, Rat.add_mul]
--         simp

--     add_comm s t := by
--         rw [← @Add.add_eq_hAdd, Add.add, instAdd]
--         simp!
--         funext n
--         exact Rat.add_comm _ _

--     left_distrib s t u := by
--         rw! [← @Add.add_eq_hAdd, Add.add, instAdd]
--         rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
--         simp!
--         funext n
--         exact Rat.mul_add _ _ _

--     right_distrib s t u := by
--         rw! [← @Add.add_eq_hAdd, Add.add, instAdd]
--         rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
--         simp!
--         funext n
--         exact Rat.add_mul _ _ _

--     zero_mul s := by
--         rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
--         rw! [OfNat.ofNat, Zero.toOfNat0, Zero.zero, instZero]
--         unfold const
--         simp

--     mul_zero s := by
--         rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
--         rw! [OfNat.ofNat, Zero.toOfNat0, Zero.zero, instZero]
--         unfold const
--         simp!

--     mul_assoc s t u := by
--         rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
--         simp!
--         funext n
--         exact Rat.mul_assoc _ _ _

--     one_mul s := by
--         rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
--         rw [OfNat.ofNat, One.toOfNat1, One.one, instOne]
--         unfold const
--         simp!

--     mul_one s := by
--         rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
--         rw [OfNat.ofNat, One.toOfNat1, One.one, instOne]
--         unfold const
--         simp!

--     zsmul i s := λ n ↦ i * s n

--     zsmul_zero' s := by
--         rw (occs := .pos [2]) [OfNat.ofNat]
--         rw [Zero.toOfNat0, Zero.zero, instZero]
--         unfold const
--         simp

--     zsmul_succ' a s := by
--         let t : Sequence ℚ := fun n => ↑↑a * s n
--         simp
--         rw [show t + s = (fun n => ↑↑a * s n + s n) by
--             exact (congrArg (HAdd.hAdd t) ∘ fun a => a) rfl
--         ]
--         funext n
--         rw [@add_one_mul]

--     zsmul_neg' a s := by
--         simp
--         let t : Sequence ℚ := fun n => (↑a + 1) * s n
--         rw [show -t = fun n => -((↑a + 1) * s n) by
--             exact (congrArg Neg.neg ∘ fun a => a) rfl
--         ]

--         funext n
--         simp [Rat.add_mul]

--     neg_add_cancel s := by
--         rw! [← @Add.add_eq_hAdd, Add.add, instAdd]
--         rw! [Neg.neg, instNeg]
--         rw! [OfNat.ofNat, Zero.toOfNat0, Zero.zero, instZero]
--         unfold const
--         simp

--     mul_comm s t := by
--         rw [← @Mul.mul_eq_hMul, Mul.mul, instMul]
--         simp
--         funext n
--         exact Rat.mul_comm _ _

-- theorem const_add (a b : ℚ) : const (a + b) = const a + const b := by
--     sorry

-- theorem add_apply (s t : Sequence ℚ) (n : ℕ) : (s + t) n = s n + t n := by
--     sorry

-- theorem neg_apply (s : Sequence ℚ) (n : ℕ) : (-s) n = -s n := by
--     sorry

-- theorem mul_apply (s t : Sequence ℚ) (n : ℕ): (s * t) n = s n * t n := by
--     sorry

-- theorem sub_apply {s t : Sequence ℚ} {n : ℕ} : (s - t) n = s n - t n := by
--     sorry

-- theorem nsmul_apply (s : Sequence ℚ) (k : ℕ) : ∀n, k • (s n) = (k • s) n := by
--     intro n
--     exact Rat.add_left_cancel (s n) rfl

-- @[simp]
-- theorem zero_eval {i : ℕ} : (0 : Sequence ℚ) i = 0 := by
--     sorry

-- @[simp]
-- theorem one_def : (const (1 : ℚ)) = 1 := by sorry

-- @[simp]
-- theorem one_eval {i : ℕ} : (1 : Sequence ℚ) i = 1 := by
--     sorry

end Sequence
