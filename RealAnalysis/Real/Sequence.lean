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
def converges (x : 𝕊 α) := ∃L, x ⟶ L

def bounded_by (x : 𝕊 α) (M : α) := M > 0 ∧ ∀i, |x i| ≤ M
def bounded (x : 𝕊 α) := ∃M, x.bounded_by M

def monotone_increasing (x : 𝕊 α) := ∀i j, i ≤ j → x i ≤ x j
def monotone_decreasing (x : 𝕊 α) := ∀i j, i ≤ j → x i ≤ x j
def monotone (x : 𝕊 α) := monotone_increasing x ∨ monotone_decreasing x

def cauchy (x : 𝕊 α) := ∀ε > 0, ∃N, ∀i > N, ∀j > N, |x i - x j| < ε

-- converges

variable {x y : 𝕊 α}

theorem neg_converges (h_x : x ⟶ A) : (-x) ⟶ (-A) := by
  intro ε ε_pos
  let ⟨N, h_N⟩ := h_x ε ε_pos
  exists N
  intro i i_ge_N
  simp
  rw [<-abs_neg]
  simp [add_comm, <-sub_eq_add_neg]
  exact h_N i i_ge_N

variable [IsStrictOrderedRing α]

theorem converges_unique (h_A : x ⟶ A) (h_B : x ⟶ B) : A = B := by
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

theorem converges_le_bound_from {L : α} (h_x : x.converges_to L) : ∃N, ∀i > N, |x i| ≤ |L| + 1 := by
  let ⟨N, _⟩ := h_x 1 (zero_lt_one)
  exists N
  grind

theorem converges_bounded {L : α} (h_x : x.converges_to L) : x.bounded := by
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

theorem add_converges (h_x : x ⟶ A) (h_y : y ⟶ B) : (x + y) ⟶ A + B := by
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

theorem sub_converges (h_x : x ⟶ A) (h_y : y ⟶ B) : (x - y) ⟶ A - B := by
  simp [sub_eq_add_neg]
  exact add_converges h_x (neg_converges h_y)

theorem mul_converges (h_x : x ⟶ A) (h_y : y ⟶ B) : (x * y) ⟶ A * B := by
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

theorem eqv_zero_mul_bounded_eqv_zero(h_x : x ⟶ 0) (h_y : y.bounded) : x * y ⟶ 0 := by
  let ⟨M, M_pos, h_y⟩ := h_y
  intro ε ε_pos

  let δ := ε/(2 * M)
  have δ_pos : δ > 0 := by exact div_pos ε_pos (by grind)
  let ⟨N, h_N⟩ := h_x δ δ_pos
  exists N
  intro i i_gt_N

  calc
    ε > ε/2 := by grind
    _ = ε/(2 * M) * M := by grind
    _ ≥ |x i| * |y i| := by gcongr <;> grind
    _ = |x i * y i| := by grind [abs_mul]
    _ = |(x * y) i - 0| := by grind [mul_on]

theorem bounded_mul_eqv_zero_eqv_zero (h_x : x.bounded) (h_y : y ⟶ 0) : x * y ⟶ 0 := by
  grind [mul_comm, eqv_zero_mul_bounded_eqv_zero]

theorem neqv_zero_gt_zero (h_x : x ⟶ L) (L_nz : L ≠ 0) : ∃m > 0, ∃N, ∀i > N, |x i| > m := by
  refine ⟨|L|/2, by grind, ?_⟩
  let ⟨N, h_x⟩ := h_x (|L|/2) (by grind)
  exists N
  grind

theorem inv_converges (h_x : x ⟶ A) (A_nz : A ≠ 0) : x⁻¹ ⟶ A⁻¹ := by
  have : |A - 1| ≥ 0 := by grind
  let ⟨m, m_pos, N₁, h_m⟩ := neqv_zero_gt_zero h_x A_nz

  intro ε ε_pos
  let δ := ε/2 * m * |A|
  have : δ > 0 := by
    repeat apply Left.mul_pos
    repeat grind

  let ⟨N₂, h_x⟩ := h_x δ (by grind)
  let N := max N₁ N₂
  exists N
  intro i i_gt_N
  calc
    ε > ε/2 := by grind
    _ = ε/2 * m * |A| / |A| / m := by grind
    _ > |x i - A|/|A|/m := by gcongr <;> grind
    _ ≥ |x i - A|/|A|/|x i| := by gcongr; simp [div_nonneg]; grind
    _ = |x i - A|/(|A| * |x i|) := by grind
    _ = |x i - A|/|A * x i| := by simp
    _ = |(x i - A)/(A * x i)| := by grind [abs_div]
    _ = |(x i)/ (A * x i) - A/(x i * A)| := by grind
    _ = |(x i)⁻¹ - A⁻¹| := by grind
    _ = |x⁻¹ i - A⁻¹| := by grind [inv_on]

theorem converge_le_forall (h_x : x ⟶ A) (h_y : y ⟶ B) (x_le_y : ∀i, x i ≤ y i) : A ≤ B := by
  by_contra!
  let ε := (A - B)/3
  have ε_pos : ε > 0 := by grind
  let ⟨Nx, h_x⟩ := h_x ε ε_pos
  let ⟨Ny, h_y⟩ := h_y ε ε_pos
  let N := max Nx Ny
  let i := N + 1
  have h_x := h_x i (by grind)
  have h_y := h_y i (by grind)
  grind

-- bounded

theorem bounded_by_ge (h_x : x.bounded_by m) (h_M : M ≥ m) : x.bounded_by M := by
  have ⟨m_pos, h_m⟩ := h_x
  exact ⟨by grind, by grind⟩

theorem converges_cauchy : x.converges → x.cauchy := by
  intro ⟨L, x_conv⟩ ε ε_pos
  let ⟨N, h_N⟩ := x_conv (ε/2) (by grind)
  exists N
  grind

theorem cauchy_bounded (h_x : x.cauchy) : x.bounded := by
  let ε : α := 1
  let ⟨N, h_x⟩ := h_x ε (by grind)

  let S : Finset α := Finset.image (fun i ↦ |x i|) (Finset.range (N + 1))
  have S_Nonempty : S.Nonempty := by
    apply Finset.image_nonempty.mpr
    exact Finset.nonempty_range_add_one

  let M₁ := Finset.max' S S_Nonempty
  have h_M₁ (i : ℕ) (h_i : i ≤ N) : |x i| ≤ M₁ := by
    apply Finset.le_max' S (|x i|)
    grind

  let M₂ := |x (N + 1)| + 1
  have h_M₂ (i : ℕ) (h_i : i > N) : |x i| ≤ M₂ := by grind [h_x i h_i (N+1)]
  let M := max M₁ M₂
  exists M
  exact And.intro (by grind) (by grind)

theorem cauchy_neqv_zero_gt_zero (h_x : x.cauchy) : (¬x ⟶ 0) → ∃m > 0, ∃N, ∀i > N, |x i| > m := by
  simp [converges_to]
  intro ε ε_pos h_nz
  refine ⟨ε/2, by grind, ?_⟩

  let ⟨N, h_x⟩ := h_x (ε/2) (by grind)
  exists N
  intro i i_gt_N
  have ⟨m, m_gt_N, h_m⟩ := h_nz N
  have h_x := h_x m m_gt_N i i_gt_N
  grind

end limits


instance [Coe α β] : Coe (𝕊 α) (𝕊 β) where
  coe := map (↑·)

@[simp]
theorem coe_on [Coe α β] (x : 𝕊 α) {i : ℕ} : (↑x : 𝕊 β) i = ↑(x i) := rfl

end Sequence
