import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Ordering.Basic

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max

import Mathlib.Algebra.Order.Field.Basic

import RealAnalysis.Real.Sequence



private abbrev converges (s : Sequence ℚ) := ∀(ε : ℚ), ε > 0 → ∃N, ∀m ≥ N, ∀n ≥ N, |s m - s n| < ε

structure Cauchy where
  seq : Sequence ℚ
  conv : converges seq


namespace Cauchy
open Sequence (map₀ const map map₂)

section basic

-- TODO simplify
theorem eq_by_seq {x y : Cauchy} : x.seq = y.seq → x = y := by
  intro h
  cases x
  subst h
  rfl

theorem eq_by_forall {x y : Cauchy} : (∀i, x.seq i = y.seq i) → x = y := by
  simpa [Sequence.eq_by] using eq_by_seq

end basic

section lifts

abbrev lifts₀ (f : ℚ) := converges (map₀ f)

def lift₀ (f : ℚ) {h_f : converges (map₀ f)} : Cauchy := by
  refine ⟨map₀ f, h_f⟩

abbrev const (a : ℚ) : Cauchy := by
  apply lift₀ a
  intro ε ε_gt_0
  exists 0
  simpa

abbrev lifts (f : ℚ → ℚ) := ∀{x : Cauchy}, converges (map f x.seq)

def lift (f : ℚ → ℚ) {h_f : lifts f} (x : Cauchy) : Cauchy := ⟨map f x.seq, h_f⟩

abbrev lifts₂ (f : ℚ → ℚ → ℚ) := ∀{x y : Cauchy}, converges (map₂ f x.seq y.seq)

def lift₂ (f : ℚ → ℚ → ℚ) {h_f : lifts₂ f} (x y : Cauchy) : Cauchy := ⟨map₂ f x.seq y.seq, h_f⟩


@[simp]
theorem lift₀_seq (f : ℚ) {h_f : lifts₀ f} : (@lift₀ f h_f).seq = map₀ f := by rfl

@[simp]
theorem lift_seq (f : ℚ → ℚ) {h_f : lifts f} {x : Cauchy}: (@lift f h_f x).seq = map f x.seq := by rfl

@[simp]
theorem lift₂_seq (f : ℚ → ℚ → ℚ) {h_f : lifts₂ f} {x y : Cauchy} : (@lift₂ f h_f x y).seq = map₂ f x.seq y.seq := rfl

theorem lifts_by (f : ℚ → ℚ)
  (h :
    ∀x : Cauchy,
    ∀ε > 0,
    ∃δ > 0,
    ∀ m n,
    |x.seq m - x.seq n| < δ →
    |map f x.seq m - map f x.seq n| < ε
  ) : lifts f := by
  intro x ε ε_gt_0
  let ⟨δ, δ_gt_0, h⟩ := h x ε ε_gt_0
  let ⟨N, x_conv⟩ := x.conv δ δ_gt_0
  exists N
  grind

theorem lifts₂_by (f : ℚ → ℚ → ℚ)
  (h :
    ∀x y : Cauchy,
    ∀ε > 0,
    ∃δ > 0,
    ∀ m n,
    |x.seq m - x.seq n| < δ →
    |y.seq m - y.seq n| < δ →
    |map₂ f x.seq y.seq m - map₂ f x.seq y.seq n| < ε
  ) : lifts₂ f := by
  intro x y ε ε_gt_0
  let ⟨δ, δ_gt_0, h⟩ := h x y ε ε_gt_0
  let ⟨N₁, x_conv⟩ := x.conv δ δ_gt_0
  let ⟨N₂, y_conv⟩ := y.conv δ δ_gt_0
  let N := max N₁ N₂
  exists N
  grind

end lifts

section bounded

def bounded_by (x : Cauchy) (M : ℚ) := ∀m, |x.seq m| ≤ M

def bounded_by_ge (x : Cauchy) (M : ℚ) (N : ℚ) : M ≤ N → x.bounded_by M → x.bounded_by N := by
  intro N_ge_M x_bounded_by_M
  rw [bounded_by] at *
  grind


-- TODO SIMPLIFY
theorem bounded (x : Cauchy) : ∃M, x.bounded_by M := by
  unfold bounded_by

  let ε : ℚ := 1
  let ⟨N, h_N⟩ := x.conv ε rfl
  rw [show ε = 1 by rfl] at *

  let S := Finset.image (fun n => |x.seq n|) (Finset.range (N + 2))
  have S_Nonempty : S.Nonempty := by
    apply Finset.image_nonempty.mpr
    exact Finset.nonempty_range_add_one

  let M := S.max' S_Nonempty + 1

  exists M

  intro m
  by_cases m ≤ N
  case pos m_le_N =>
    suffices h : |x.seq m| ≤ S.max' S_Nonempty by grind only
    apply Finset.le_max'
    apply Finset.mem_image_of_mem (fun n => |x.seq n|)
    apply Finset.mem_range.mpr
    apply Nat.lt_add_right 1
    exact Nat.lt_succ_of_le m_le_N

  case neg m_gt_N =>
    rw [not_le] at m_gt_N
    calc
      |x.seq m| = |x.seq (N + 1) + (x.seq m - x.seq (N + 1))| := by simp
      _ ≤ |x.seq (N + 1)| + |x.seq m - x.seq (N + 1)| := abs_add_le (x.seq (N + 1)) (x.seq m - x.seq (N + 1))
      _ ≤ |x.seq (N + 1)| + 1 := by grind only
      _ ≤ M := by
        simp [M]
        apply Finset.le_max'
        apply Finset.mem_image_of_mem (fun n => |x.seq n|)
        exact Finset.self_mem_range_succ (N + 1)

theorem bounded_by_pos (x : Cauchy) (M : ℚ) : x.bounded_by M → M ≥ 0 := by
  intro x_bounded_by_M
  have M_ge := (x_bounded_by_M 0).ge
  grind

end bounded

section arithmetic

theorem add_lifts : lifts₂ (·+·) := by
  apply lifts₂_by
  intro x y ε ε_gt_0
  refine ⟨ε/2, by grind, ?_⟩
  simp
  grind

instance : Add Cauchy := ⟨@lift₂ (·+·) add_lifts⟩

@[simp]
theorem add_seq_on (x y : Cauchy) {i : ℕ} : (x + y).seq i = x.seq i + y.seq i := by rfl

theorem const_add (a b : ℚ) : const (a + b) = const a + const b := by rfl

instance : Zero Cauchy := ⟨const 0⟩

@[simp]
theorem zero_seq_on {i : ℕ} : seq 0 i = 0 := by rfl

theorem neg_lifts : lifts (-·) := by
  apply lifts_by
  intro x ε ε_gt_0
  refine ⟨ε, ε_gt_0, ?_⟩
  simp
  grind

instance : Neg Cauchy := ⟨@lift (-·) neg_lifts⟩

@[simp]
theorem neg_seq_on (x : Cauchy) {i : ℕ} : (-x).seq i = -x.seq i := by rfl

theorem mul_lifts : lifts₂ (·*·) := by
  apply lifts₂_by
  intro x y

  let X := x.bounded.choose + 1
  have h_X : x.bounded_by X := bounded_by_ge x x.bounded.choose X (by grind) x.bounded.choose_spec
  have X_ge_1 : X ≥ 1 := by grind [x.bounded_by_pos x.bounded.choose x.bounded.choose_spec]

  let Y := y.bounded.choose + 1
  have h_Y : y.bounded_by Y := bounded_by_ge y y.bounded.choose Y (by grind) y.bounded.choose_spec
  have Y_ge_1 : Y ≥ 1 := by grind [y.bounded_by_pos y.bounded.choose y.bounded.choose_spec]

  intro ε ε_gt_0

  let δ := ε/4/X/Y
  have δ_gt_0 : δ > 0 := by
    repeat (refine (Rat.lt_div_iff ?_).mpr ?_; grind; simp)
    exact ε_gt_0

  refine ⟨δ, δ_gt_0, ?_⟩

  intro m n x_conv y_conv

  calc
    ε > ε/4 + ε/4 := by grind
    _ ≥ ε/4/Y + ε/4/X := by
      have lt : ∀a ≥ 1, ε/4 ≥ ε/4/a := by
        intro a a_gt_1
        rw [@div_right_comm]
        gcongr
        . rfl
        . rw [Rat.div_def, (mul_le_iff_le_one_right ε_gt_0)]
          exact inv_le_one_of_one_le₀ a_gt_1
      grind [lt X X_ge_1, lt Y Y_ge_1]
    _ = X*ε/4/X/Y + Y*ε/4/X/Y := by grind
    _ ≥ |x.seq m| * ε/4/X/Y + |y.seq n| * ε/4/X/Y := by
      gcongr <;> grind [h_X m, h_Y n]
    _ = |x.seq m| * δ + |y.seq n| * δ := by subst δ; grind
    _ ≥ |x.seq m| * |y.seq m - y.seq n| + |y.seq n| * |x.seq m - x.seq n| := by
      gcongr
      . exact abs_nonneg (x.seq m)
      . exact abs_nonneg (y.seq n)
    _ = |x.seq m * (y.seq m - y.seq n)| + |y.seq n * (x.seq m - x.seq n)| := by simp [abs_mul]
    _ ≥ |x.seq m * (y.seq m - y.seq n) + y.seq n * (x.seq m - x.seq n)| := abs_add_le _ _
    _ = |x.seq m * y.seq m - x.seq n * y.seq n| := by grind [mul_sub]

instance : Mul Cauchy := ⟨@lift₂ (·*·) mul_lifts⟩

@[simp]
theorem mul_seq_on (x y : Cauchy) {i : ℕ} : (x * y).seq i = x.seq i * y.seq i := by rfl

instance : One Cauchy := ⟨const 1⟩

@[simp]
theorem one_seq_on {i : ℕ} : seq 1 i = 1 := by rfl


instance : CommRing Cauchy where
  add_assoc x y z := by
    apply eq_by_forall
    grind [add_seq_on]

  zero_add x := by
    apply eq_by_forall
    simp [add_seq_on]

  add_zero x := by
    apply eq_by_forall
    simp [add_seq_on]

  add_comm x y := by
    apply eq_by_forall
    grind [add_seq_on]

  neg_add_cancel x := by
    apply eq_by_forall
    simp [add_seq_on, neg_seq_on]

  left_distrib x y z := by
    apply eq_by_forall
    grind [add_seq_on, mul_seq_on]

  right_distrib x y z := by
    apply eq_by_forall
    grind [add_seq_on, mul_seq_on]

  zero_mul x := by
    apply eq_by_forall
    simp [mul_seq_on]

  mul_zero x := by
    apply eq_by_forall
    simp [mul_seq_on]

  mul_assoc x y z := by
    apply eq_by_forall
    grind [mul_seq_on]

  one_mul x := by
    apply eq_by_forall
    simp [mul_seq_on]

  mul_one x := by
    apply eq_by_forall
    simp [mul_seq_on]

  mul_comm x y := by
    apply eq_by_forall
    grind [mul_seq_on]

  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp]
theorem sub_seq_on (x y : Cauchy) : ∀i, (x - y).seq i = x.seq i - y.seq i := by
  simp [sub_eq_add_neg]

end arithmetic

section equivalence

abbrev eqv_zero (s : Sequence ℚ) := ∀ε > 0, ∃N, ∀n ≥ N, |s n - 0| < ε

instance : Setoid Cauchy where
  r x y := eqv_zero (x - y).seq
  iseqv := by
    apply Equivalence.mk

    case refl =>
      intro x ε ε_gt_0
      exists 1
      simp
      grind

    case symm =>
      intro x y h
      simp [eqv_zero, sub_seq_on] at h
      simpa [eqv_zero, sub_seq_on, abs_sub_comm]

    case trans =>
        intro x y z x_eqv_y y_eqv_z ε ε_gt_0

        have ⟨N₁, x_eqv_y⟩ := x_eqv_y (ε/2) (div_pos ε_gt_0 rfl)
        have ⟨N₂, y_eqv_z⟩ := y_eqv_z (ε/2) (div_pos ε_gt_0 rfl)

        let N := max N₁ N₂
        exists N
        intro n n_ge_N
        simp [sub_seq_on] at *
        grind

theorem equiv_iff {x y : Cauchy} : x ≈ y ↔ ∀ε > 0, ∃N, ∀n ≥ N, |x.seq n - y.seq n| < ε := by
  unfold HasEquiv.Equiv instHasEquivOfSetoid instSetoid
  simp [eqv_zero]

abbrev interleave {x y : Cauchy} (x_eqv_y : x ≈ y) : Cauchy := by
  let s : Sequence ℚ := fun i ↦ if Even i then x.seq (i/2) else y.seq (i/2)
  refine ⟨s, ?_⟩
  intro ε ε_gt_0
  let ⟨N₁, x_conv⟩ := x.conv (ε/2) (by grind)
  let ⟨N₂, y_conv⟩ := y.conv (ε/2) (by grind)
  let ⟨N₃, eqv⟩ := x_eqv_y (ε/2) (by grind)
  simp [] at eqv
  let N := 2 * max N₁ (max N₂ N₃)
  exists N
  intro m m_ge_N n n_ge_N
  have x_conv := x_conv (m/2) (by grind) (n/2) (by grind)
  have y_conv := y_conv (m/2) (by grind) (n/2) (by grind)

  unfold s
  split <;> split <;> grind

theorem lift_eqv (f : ℚ → ℚ) {h_f : lifts f} {x y : Cauchy} (x_eqv_y : x ≈ y) : @lift f h_f x ≈ @lift f h_f y := by
  let z : Cauchy := @lift f h_f $ interleave x_eqv_y

  intro ε ε_gt_0
  let ⟨N, z_conv⟩ := z.conv ε ε_gt_0

  exists N
  intro n n_ge_N
  simp [z, sub_seq_on] at *
  have z_conv := z_conv (2*n) (by grind) (2*n+1) (by grind)
  grind

theorem lift₂_eqv (f : ℚ → ℚ → ℚ) {h_f : lifts₂ f} {x₁ x₂ y₁ y₂ : Cauchy}
                  : x₁ ≈ x₂ → y₁ ≈ y₂ → @lift₂ f h_f x₁ y₁ ≈ @lift₂ f h_f x₂ y₂ := by
  intro x₁_eqv_x₂ y₁_eqv_y₂ ε ε_gt_0
  simp [lifts₂, converges] at h_f

  let x := interleave x₁_eqv_x₂
  let y := interleave y₁_eqv_y₂
  let z := @lift₂ f h_f x y
  let ⟨N, z_conv⟩ := z.conv ε ε_gt_0

  exists N
  intro n n_ge_N
  simp [z] at *
  have z_conv := z_conv (2*n) (by grind) (2*n+1) (by grind)
  grind

theorem add_eqv {x₁ y₁ x₂ y₂ : Cauchy} : x₁ ≈ x₂ → y₁ ≈ y₂ → x₁+y₁ ≈ x₂+y₂ := by apply lift₂_eqv (·+·)

theorem neg_eqv {x y : Cauchy} : x ≈ y →  (-x) ≈ (-y) := by apply lift_eqv (-·)

theorem mul_eqv {x₁ y₁ x₂ y₂ : Cauchy} : x₁ ≈ x₂ → y₁ ≈ y₂ → x₁*y₁ ≈ x₂*y₂ := by apply lift₂_eqv (·*·)

-- INV
-- TODO remove
theorem nz_ge_zero (x : Cauchy) (x_nz : ¬x ≈ 0) : ∃m > 0, ∃N, ∀n ≥ N, |x.seq n| ≥ m := by
  simp [equiv_iff] at x_nz
  let ⟨ε, ε_gt_0, limit⟩ := x_nz
  refine ⟨ε/2, by grind, ?_⟩

  let ⟨N, x_conv⟩ := x.conv (ε/2) (by grind)
  exists N
  intro n n_ge_N

  have ⟨m, m_ge_N, h_m⟩ := limit N
  have x_conv := x_conv m m_ge_N n n_ge_N
  grind

theorem nz_gt_zero (x : Cauchy) (x_nz: ¬x ≈ 0) : ∃m > 0, ∃N, ∀n ≥ N, |x.seq n| > m := by
  let ⟨m, m_pos, N, h_N⟩ := nz_ge_zero x x_nz
  refine ⟨m/2, by grind, ?_⟩
  exists N
  grind

theorem exists_inv (x : Cauchy) (x_nz : ¬x ≈ 0) : ∃y, x * y ≈ 1 := by
  let m_pos := (nz_gt_zero x x_nz).choose_spec.left
  let h_m := (nz_gt_zero x x_nz).choose_spec.right.choose_spec
  set m := (nz_gt_zero x x_nz).choose
  set N := (nz_gt_zero x x_nz).choose_spec.right.choose

  let y_seq : Sequence ℚ := fun i ↦ if i ≥ N then (x.seq i)⁻¹ else 0

  have : converges y_seq := by
    intro ε ε_gt_0
    have h_m2 : m^2 > 0 := Rat.pow_pos m_pos
    have ⟨M, x_conv⟩ := x.conv (m^2 * ε / 2) (by
      simp [Rat.div_def, Rat.mul_pos h_m2 ε_gt_0]
    )

    let N := max N M
    exists N
    intro i i_gt_N j j_gt_N

    have x_conv := x_conv i (by grind) j (by grind)
    have h_i := h_m i (by grind)
    have h_j := h_m j (by grind)
    have h_ij : |x.seq i * x.seq j| ≥ m^2 := by simp [sq]; gcongr; grind

    calc
      ε > ε/2 := by grind
      _ = m^2 * ε / 2 / m^2 := by grind
      _ > |x.seq i - x.seq j|/m^2 := by gcongr
      _ ≥ |x.seq i - x.seq j|/|x.seq i * x.seq j| := by gcongr; grind
      _ = |x.seq j - x.seq i|/|x.seq i * x.seq j| := by grind
      _ = |(x.seq j - x.seq i)/(x.seq i * x.seq j)| := by simp [Rat.div_def]
      _ = |1/(x.seq i) - 1/(x.seq j)| := by grind
      _ = |y_seq i - y_seq j| := by grind

  exists ⟨y_seq, this⟩

  intro ε ε_gt_0
  exists N
  intro i i_ge_N
  simp
  grind

noncomputable instance : Inv Cauchy where
  inv x := by
    by_cases x ≈ 0
    case pos _ => exact 0
    case neg h_x => exact (exists_inv x h_x).choose

theorem mul_inv_eqv_cancel {x : Cauchy} (x_nz : ¬x ≈ 0) : x * x⁻¹ ≈ 1 := by
  simp [Inv.inv, x_nz]
  grind

theorem one_neqv_zero : ¬(1 : Cauchy) ≈ 0 := by
  simp [equiv_iff]
  refine ⟨1, rfl, ?_⟩
  intro N
  refine ⟨⟨N, by rfl⟩, ?_⟩
  simp

theorem inv_eqv_zero {x : Cauchy} : x ≈ 0 → x⁻¹ = 0 := by
  intro x_eqv_0
  simp [Inv.inv]
  intro h
  contradiction

theorem eqv_inv_iff {x y : Cauchy} (y_nz : ¬y ≈ 0) : x ≈ y⁻¹ ↔ x * y ≈ 1 := by
  apply Iff.intro
  . intro y_inv
    calc
      x * y ≈ x * y := Setoid.refl (x * y)
      _ = y * x := mul_comm x y
      _ ≈ y * y⁻¹ := mul_eqv (Setoid.refl y) y_inv
      _ ≈ 1 := mul_inv_eqv_cancel y_nz

  . intro xy_cancel
    calc
      x ≈ x := Setoid.refl x
      _ = x * 1 := (mul_one x).symm
      _ ≈ x * (y * y⁻¹) := mul_eqv (Setoid.refl x) (Setoid.symm (mul_inv_eqv_cancel y_nz))
      _ = (x * y) * y⁻¹ := (mul_assoc x y y⁻¹).symm
      _ ≈ 1 * y⁻¹ := mul_eqv xy_cancel (Setoid.refl y⁻¹)
      _ = y⁻¹ := one_mul y⁻¹

theorem inv_eqv {x y : Cauchy} : x ≈ y → x⁻¹ ≈ y⁻¹ := by
  intro x_eqv_y
  by_cases x ≈ 0
  case pos x_eqv_0 =>
    rw [inv_eqv_zero x_eqv_0]
    have y_eqv_0 : y ≈ 0 := Setoid.trans (Setoid.symm x_eqv_y) x_eqv_0
    rw [inv_eqv_zero y_eqv_0]
    exact Setoid.refl 0

  rename _ => x_nz
  have y_nz : ¬y ≈ 0 := by
    intro y_eqv_0
    have := Setoid.trans x_eqv_y y_eqv_0
    contradiction

  apply (eqv_inv_iff y_nz).mpr
  apply Setoid.symm
  calc
    1 ≈ x * x⁻¹ := Setoid.symm (mul_inv_eqv_cancel x_nz)
    _ = x⁻¹ * x := mul_comm x x⁻¹
    _ ≈ x⁻¹ * y := mul_eqv (Setoid.refl x⁻¹) x_eqv_y




end equivalence

section order

instance instLE : LE Cauchy where
  le x y := ∃N, ∀n ≥ N, x.seq n ≥ y.seq n

theorem le_eqv {x₁ y₁ x₂ y₂ : Cauchy} : x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ ≤ y₁) = (x₂ ≤ y₂) := by
  intro x_eqv y_eqv
  by_cases h_le : x₁ ≤ y₁
  case pos =>
    simp [h_le]
    sorry
    --let ⟨N,h_N⟩ := h_le
  unfold LE.le instLE
  simp
  sorry


end order

end Cauchy
