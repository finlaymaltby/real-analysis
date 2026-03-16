import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Ordering.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Order.Lattice

def Sequence (α: Type u) := ℕ -> α

namespace Sequence

def cons (a : α) (s : Sequence α) : Sequence α
    | 0 => a
    | n => s (n - 1)

def get (s : Sequence α) (n : ℕ) : α := s n

def const (a : α) : Sequence α := fun _ ↦ a

instance [Add α] : Add (Sequence α) where
    add (s₁ s₂ : Sequence α) := λ n ↦ s₁ n + s₂ n

instance [Zero α] : Zero (Sequence α) where
    zero := const 0

instance [Neg α] : Neg (Sequence α) where
    neg (s₁ : Sequence α) := λ n ↦ -s₁ n

instance [Mul α] : Mul (Sequence α) where
    mul (s₁ s₂ : Sequence α) := λ n ↦ (s₁ n) * (s₂ n)

instance [One α] : One (Sequence α) where
    one := const 1

instance [Inv α] : Inv (Sequence α) where
    inv s := λ n ↦ Inv.inv (s n)


instance [HMul α β β] : SMul α (Sequence β) where
    smul m s := λ n ↦ m * s n

instance : CommRing (Sequence ℚ) where
    add_assoc s t u := by
        rw [← @Add.add_eq_hAdd, Add.add, instAdd]
        simp!
        funext n
        exact Rat.add_assoc _ _ _

    zero_add s := by
        rw [← @Add.add_eq_hAdd, Add.add, instAdd]
        simp!
        funext n
        exact add_eq_right.mpr rfl

    add_zero s := by
        rw [← @Add.add_eq_hAdd, Add.add, instAdd]
        simp!
        funext n
        exact add_eq_left.mpr rfl

    nsmul a s := λ n ↦ a * s n

    nsmul_zero s := by
        rw [@Rat.natCast_ofNat]
        rw (occs := .pos [2]) [OfNat.ofNat]
        rw [Zero.toOfNat0, Zero.zero, instZero]
        simp
        rfl

    nsmul_succ a s := by
        let t : Sequence ℚ := fun n => ↑a * s n
        rw [show t + s = (fun n => ↑a * s n + s n) by
            exact (congrArg (HAdd.hAdd t) ∘ fun a => a) rfl
        ]
        funext n
        rw [Rat.natCast_add, Rat.add_mul]
        simp

    add_comm s t := by
        rw [← @Add.add_eq_hAdd, Add.add, instAdd]
        simp!
        funext n
        exact Rat.add_comm _ _

    left_distrib s t u := by
        rw! [← @Add.add_eq_hAdd, Add.add, instAdd]
        rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
        simp!
        funext n
        exact Rat.mul_add _ _ _

    right_distrib s t u := by
        rw! [← @Add.add_eq_hAdd, Add.add, instAdd]
        rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
        simp!
        funext n
        exact Rat.add_mul _ _ _

    zero_mul s := by
        rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
        rw! [OfNat.ofNat, Zero.toOfNat0, Zero.zero, instZero]
        unfold const
        simp

    mul_zero s := by
        rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
        rw! [OfNat.ofNat, Zero.toOfNat0, Zero.zero, instZero]
        unfold const
        simp!

    mul_assoc s t u := by
        rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
        simp!
        funext n
        exact Rat.mul_assoc _ _ _

    one_mul s := by
        rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
        rw [OfNat.ofNat, One.toOfNat1, One.one, instOne]
        unfold const
        simp!

    mul_one s := by
        rw! [← @Mul.mul_eq_hMul, Mul.mul, instMul]
        rw [OfNat.ofNat, One.toOfNat1, One.one, instOne]
        unfold const
        simp!

    zsmul i s := λ n ↦ i * s n

    zsmul_zero' s := by
        rw (occs := .pos [2]) [OfNat.ofNat]
        rw [Zero.toOfNat0, Zero.zero, instZero]
        unfold const
        simp

    zsmul_succ' a s := by
        let t : Sequence ℚ := fun n => ↑↑a * s n
        simp
        rw [show t + s = (fun n => ↑↑a * s n + s n) by
            exact (congrArg (HAdd.hAdd t) ∘ fun a => a) rfl
        ]
        funext n
        rw [@add_one_mul]

    zsmul_neg' a s := by
        simp
        let t : Sequence ℚ := fun n => (↑a + 1) * s n
        rw [show -t = fun n => -((↑a + 1) * s n) by
            exact (congrArg Neg.neg ∘ fun a => a) rfl
        ]

        funext n
        simp [Rat.add_mul]

    neg_add_cancel s := by
        rw! [← @Add.add_eq_hAdd, Add.add, instAdd]
        rw! [Neg.neg, instNeg]
        rw! [OfNat.ofNat, Zero.toOfNat0, Zero.zero, instZero]
        unfold const
        simp

    mul_comm s t := by
        rw [← @Mul.mul_eq_hMul, Mul.mul, instMul]
        simp
        funext n
        exact Rat.mul_comm _ _

theorem const_add (a b : ℚ) : const (a + b) = const a + const b := by
    sorry

@[simp]
theorem one_def : const 1 = (1 : Sequence ℚ) := by rfl

theorem add_distrib (s t : Sequence ℚ) (n : ℕ) : (s + t) n = s n + t n := by
    sorry

theorem mul_distrib (s t : Sequence ℚ) (n : ℕ): (s * t) n = s n * t n := by
    sorry


theorem nsmul_distrib (s : Sequence ℚ) (k : ℕ) : ∀n, k • (s n) = (k • s) n := by
    intro n
    exact Rat.add_left_cancel (s n) rfl


theorem zero_zeroes : ∀n, (0 : Sequence ℚ) n = 0 := by
    intro n
    rw (occs := .pos [1]) [OfNat.ofNat]
    unfold Zero.toOfNat0 Zero.zero instZero
    unfold const
    simp

end Sequence


instance : Setoid (Sequence ℚ) where
    r x y := ∀(ε : ℚ), ε > 0 → ∃N, ∀n > N, abs (x n - y n) < ε
    iseqv := by
        apply Equivalence.mk

        case refl =>
            intro x ε ε_gt_0
            exists 1
            intro n n_gt_1
            simp
            exact ε_gt_0.dual

        case symm =>
            intro x y x_eqv_y ε ε_gt_0
            simp [abs_sub_comm]
            exact x_eqv_y ε ε_gt_0

        case trans =>
            intro x y z x_eqv_y y_eqv_z ε ε_gt_0

            have x_eqv_y := x_eqv_y (ε/2) (div_pos ε_gt_0 rfl)
            have y_eqv_z := y_eqv_z (ε/2) (div_pos ε_gt_0 rfl)

            let N := max x_eqv_y.choose y_eqv_z.choose
            exists N
            intro n n_gt_N

            have x_eqv_y := x_eqv_y.choose_spec n (sup_lt_iff.mp n_gt_N).left
            have y_eqv_z := y_eqv_z.choose_spec n (sup_lt_iff.mp n_gt_N).right

            have := add_lt_add x_eqv_y y_eqv_z
            simp [add_halves] at this
            rw [<-gt_iff_lt] at *

            calc
                ε > |x n - y n| + |y n - z n| := this
                _ ≥ |x n - y n + (y n - z n)| := (abs_add_le (x n - y n) (y n - z n)).ge
                _ ≥ |x n - z n| := by simp
