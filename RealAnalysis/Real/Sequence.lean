import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Ordering.Basic

import Mathlib.Order.Lattice
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max

def Sequence (α: Type u) := ℕ -> α

notation "𝕊" => Sequence

namespace Sequence

section basic

def eq_by_forall {x y : 𝕊 α} : (∀i, x i = y i) ↔ x = y := by
  apply Iff.intro
  . intro h
    funext i
    exact h i
  . intro h i
    subst h
    rfl

def map₀ (a : α) : 𝕊 α := fun _ ↦ a

def map (f : α → β) (x : 𝕊 α) := fun i ↦ f (x i)

def map₂ (f : α → β → γ) (x : 𝕊 α) (y : 𝕊 β) := fun i ↦ f (x i) (y i)

@[simp]
theorem map₀_on (a : α) {i : ℕ} : map₀ a i = a := rfl

@[simp]
theorem map_on (f : α → β) (x : 𝕊 α) : map f x i = f (x i) := rfl

@[simp]
theorem map₂_on (f : α → β → γ) (x : 𝕊 α) (y : 𝕊 β) {i : ℕ} : map₂ f x y i = f (x i) (y i) := rfl

end basic

section arithmetic

instance [Add α] : Add (𝕊 α) := ⟨map₂ (·+·)⟩
@[simp]
theorem add_on [Add α] (x y : 𝕊 α) {i : ℕ} : (x + y) i = x i + y i := map₂_on (·+·) x y

instance [Zero α] : Zero (𝕊 α) := ⟨map₀ 0⟩
@[simp]
theorem zero_on [Zero α] {i : ℕ} : (0 : 𝕊 α) i = 0 := map₀_on 0

instance [Neg α] : Neg (𝕊 α) := ⟨map (-·)⟩
@[simp]
theorem neg_on [Neg α] (x : 𝕊 α) {i : ℕ} : (-x) i = -x i := map_on (-·) x

instance [Mul α] : Mul (𝕊 α) := ⟨map₂ (·*·)⟩
@[simp]
theorem mul_on [Mul α] (x y : 𝕊 α) {i : ℕ} : (x * y) i = x i * y i := map₂_on (·*·) x y

instance [Inv α] : Inv (𝕊 α) := ⟨map (·⁻¹)⟩
@[simp]
theorem inv_on [Inv α] (x : 𝕊 α) {i : ℕ} : x⁻¹ i = (x i)⁻¹ := map_on (·⁻¹) x

instance [One α] : One (𝕊 α) := ⟨map₀ 1⟩
@[simp]
theorem one_on [One α] {i : ℕ} : (1 : 𝕊 α) i = 1 := map₀_on 1

instance [CommRing α] : CommRing (𝕊 α) where
  add_assoc x y z := by apply eq_by_forall.mp; simp; grind
  zero_add x := by apply eq_by_forall.mp; simp
  add_zero x := by apply eq_by_forall.mp; simp
  add_comm x y := by apply eq_by_forall.mp; simp; grind
  neg_add_cancel x := by apply eq_by_forall.mp; simp
  left_distrib x y z := by apply eq_by_forall.mp; simp; grind
  right_distrib x y z := by apply eq_by_forall.mp; simp; grind
  zero_mul x := by apply eq_by_forall.mp; simp
  mul_zero x := by apply eq_by_forall.mp; simp
  mul_assoc x y z := by apply eq_by_forall.mp; simp; grind
  one_mul x := by apply eq_by_forall.mp; simp
  mul_one x := by apply eq_by_forall.mp; simp
  mul_comm x y := by apply eq_by_forall.mp; simp; grind
  nsmul := nsmulRec
  zsmul := zsmulRec


@[simp]
theorem sub_on [CommRing α] (x y : 𝕊 α) {i : ℕ} : (x - y) i = x i - y i := by simp [sub_eq_add_neg]

end arithmetic

section limits

variable {α : Type} [Field α] [LinearOrder α]

def converges_to (x : 𝕊 α) (L : α) := ∀ε > 0, ∃(N : ℕ), ∀i > N, |x i - L| < ε
infix:50 "⟶" => converges_to

theorem neg_converges {x : 𝕊 α} (h_x : x ⟶ A) : (-x) ⟶ (-A) := by
  intro ε ε_pos
  let ⟨N, h_N⟩ := h_x ε ε_pos
  exists N
  intro i i_ge_N
  simp
  rw [<-abs_neg]
  simp [add_comm, <-sub_eq_add_neg]
  exact h_N i i_ge_N

def bounded_by (x : 𝕊 α) (M : α) := M > 0 ∧ ∀i, |x i| ≤ M
def monotone (x : 𝕊 α) := ∀i j, i ≤ j → x i ≤ x j

variable [IsStrictOrderedRing α]

theorem converges_unique {x : 𝕊 α} (h_A : x ⟶ A) (h_B : x ⟶ B) : A = B := by
  by_contra! h
  have : |A - B| > 0 := abs_pos.mpr (sub_ne_zero_of_ne h)
  let ε := |A - B|/2
  have ε_pos : ε > 0 := half_pos this

  let ⟨Na, h_Na⟩ := h_A ε ε_pos
  let ⟨Nb, h_Nb⟩ := h_B ε ε_pos
  let N := max Na Nb

  have h_Na := h_Na (N + 1) (by grind)
  have h_Nb := h_Nb (N + 1) (by grind)
  grind

theorem converges_le_bound_from {x : 𝕊 α} {L : α} (h_x : converges_to x L) : ∃N, ∀i > N, |x i| ≤ |L| + 1 := by
  let ⟨N, _⟩ := h_x 1 (zero_lt_one)
  exists N
  grind

theorem converges_bounded {x : 𝕊 α} {L : α} (h_x : converges_to x L) : ∃M, x.bounded_by M := by
  let ⟨N, h_N⟩ := converges_le_bound_from h_x
  have : |L| + 1 > 0 := add_pos_of_nonneg_of_pos (abs_nonneg L) zero_lt_one

  let S : Finset α := Finset.image (fun i ↦ |x i|) (Finset.range (N + 1))
  have S_Nonempty : S.Nonempty := by
    apply Finset.image_nonempty.mpr
    exact Finset.nonempty_range_add_one

  let M₁ := Finset.max' S S_Nonempty
  have h_M₁ (i : ℕ) (h_i : i ≤ N) : |x i| ≤ M₁ := by
    apply Finset.le_max' S (|x i|)
    grind

  let M := max M₁ (|L| + 1)

  refine ⟨M, by grind, ?_⟩
  grind

theorem add_converges {x y : 𝕊 α} (h_x : x ⟶ A) (h_y : y ⟶ B) : (x + y) ⟶ A + B := by
  intro ε ε_pos
  let δ := ε/2
  have δ_pos : δ > 0 := div_pos ε_pos zero_lt_two
  let ⟨Nx, h_Nx⟩ := h_x δ δ_pos
  let ⟨Ny, h_Ny⟩ := h_y δ δ_pos
  let N := max Nx Ny
  exists N
  intro i i_ge_N

  let h_Nₛ := h_Nx i (by grind)
  let h_Nₜ := h_Ny i (by grind)

  calc
    ε = δ + δ := by grind
    _ > |x i - A| + |y i - B| := add_lt_add h_Nₛ h_Nₜ
    _ ≥ |x i - A + (y i - B)| := abs_add_le (x i - A) (y i - B)
    _ = |x i + y i - (A + B)| := by grind
    _ = |(x + y) i - (A + B)| := by simp [<-add_on]

theorem sub_converges {x y : 𝕊 α} (h_x : x ⟶ A) (h_y : y ⟶ B) : (x - y) ⟶ A - B := by
  simp [sub_eq_add_neg]
  exact add_converges h_x (neg_converges h_y)

theorem mul_converges {x y : 𝕊 α} (h_x : x ⟶ A) (h_y : y ⟶ B) : (x * y) ⟶ A * B := by
  let ⟨N₁ , h_N₁⟩ := converges_le_bound_from h_x
  let h_A_pos := add_pos_of_nonneg_of_pos (abs_nonneg A) zero_lt_one

  let M := max |B| (|A| + 1)
  have M_pos : M > 0 := by grind
  have h_M : ∀i > N₁, |x i| ≤ M := by grind

  intro ε ε_pos
  let δ := ε/2/M
  have δ_pos : δ > 0 := by
    apply div_pos
    . exact half_pos ε_pos
    . exact M_pos

  let ⟨Nx, h_Nx⟩ := h_x δ δ_pos
  let ⟨Ny, h_Ny⟩ := h_y δ δ_pos

  let N := max N₁ (max Nx Ny)
  exists N
  intro i i_gt_N

  calc
    ε = ε/2 + ε/2 := by grind
    _ = M * (ε/2/M) + M * (ε/2/M) := by grind
    _ > M * |y i - B| + M * |x i - A| := by gcongr <;> grind
    _ ≥ |x i| * |y i - B| + |B| * |x i - A| := by gcongr <;> grind
    _ = |(x i) * (y i - B)| + |B * (x i - A)| := by simp
    _ ≥ |(x i) * (y i - B) + B * (x i - A)| := abs_add_le _ _
    _ = |(x i) * (y i) - A * B| := by grind
    _ = |(x * y) i - A * B| := by simp

instance : Setoid (Sequence α) where
  r x y := (x - y).converges_to 0
  iseqv := by
    apply Equivalence.mk

    case refl =>
      intro x ε ε_pos
      exists 0
      simp
      grind

    case symm =>
      intro x y h

      simp [converges_to] at h
      simpa [converges_to, abs_sub_comm]

    case trans =>
        intro x y z x_eqv_y y_eqv_z ε ε_pos

        have ⟨N₁, x_eqv_y⟩ := x_eqv_y (ε/2) (half_pos ε_pos)
        have ⟨N₂, y_eqv_z⟩ := y_eqv_z (ε/2) (half_pos ε_pos)

        let N := max N₁ N₂
        exists N
        intro n n_ge_N
        simp_all
        grind

theorem eqv_iff {x y : 𝕊 α} : x ≈ y ↔ (x - y).converges_to 0 := by
  unfold HasEquiv.Equiv instHasEquivOfSetoid instSetoid
  simp

theorem eqv_zero_iff_converges_zero {x : 𝕊 α} : x ⟶ 0 ↔ x ≈ 0 := by simp [eqv_iff]

theorem inv_converges {x : 𝕊 α} (h_x : x ⟶ A) (A_nz : A ≠ 0) : x⁻¹ ⟶ A⁻¹ := by
  have h_x : ¬(x ⟶ 0) := fun h_zero ↦ A_nz (converges_unique h_x h_zero)
  simp [converges_to] at h_x
  let ⟨ε, ε_pos, h_x⟩ := h_x
  sorry


end limits

end Sequence
