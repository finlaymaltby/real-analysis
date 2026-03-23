import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Ordering.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max

import Mathlib.Algebra.Order.Field.Basic

import RealAnalysis.Real.Sequence

private def converges (seq : Sequence ℚ) := ∀(ε : ℚ), ε > 0 → ∃N, ∀m ≥ N, ∀n ≥ N, |seq m - seq n| < ε

structure Cauchy where
  seq : Sequence ℚ
  conv : converges seq

namespace Cauchy

def const (a : ℚ) : Cauchy := by
  refine ⟨fun _ => a, ?_ ⟩
  intro ε ε_gt_0
  exists 0
  intro n n_gt_0 m m_gt_0
  simp
  exact ε_gt_0

@[simp]
theorem const_seq_const (a : ℚ) : (const a).seq = Sequence.const a := by rfl

def lift (f : Sequence ℚ -> Sequence ℚ) (x : Cauchy)  (conv : ∀ε > 0, ∃δ > 0,
  ∀ m n, (|x.seq m - x.seq n| < δ) → |(f x.seq) m - (f x.seq) n| < ε)
  : Cauchy := ⟨f x.seq, by
    intro ε ε_gt_0

    let ⟨δ, δ_gt_0, conv⟩ := conv ε ε_gt_0

    let ⟨N, h_N⟩ := x.conv δ δ_gt_0
    exists N
    intro m m_lt_N n n_lt_N

    have x_conv := h_N m m_lt_N n n_lt_N

    exact conv m n x_conv
  ⟩

def lift₂ (x y : Cauchy) (f : Sequence ℚ → Sequence ℚ → Sequence ℚ) (conv : ∀ε > 0, ∃δx > 0, ∃δy > 0,
   (∀ m n, (|x.seq m - x.seq n| < δx) → (|y.seq m - y.seq n| < δy) → |(f x.seq y.seq) m - (f x.seq y.seq) n| < ε))
  : Cauchy := ⟨f x.seq y.seq, by
    intro ε ε_gt_0

    let ⟨δx, δx_gt_0, δy, δy_gt_0, conv⟩ := conv ε ε_gt_0

    have x_conv := x.conv δx δx_gt_0
    have y_conv := y.conv δy δy_gt_0

    let N := max x_conv.choose y_conv.choose
    exists N
    intro m m_lt_N n n_lt_N

    have x_conv := x_conv.choose_spec
      m (sup_le_iff.mp m_lt_N).left
      n (sup_le_iff.mp n_lt_N).left
    have y_conv := y_conv.choose_spec
      m (sup_le_iff.mp m_lt_N).right
      n (sup_le_iff.mp n_lt_N).right

    exact conv m n x_conv y_conv
⟩

def lift₂_single (x y : Cauchy) (f : Sequence ℚ → Sequence ℚ → Sequence ℚ) (conv : ∀ε > 0, ∃δ > 0,
   (∀ m n, (|x.seq m - x.seq n| < δ) → (|y.seq m - y.seq n| < δ) → |(f x.seq y.seq) m - (f x.seq y.seq) n| < ε))
  : Cauchy := ⟨f x.seq y.seq, by
    intro ε ε_gt_0

    let ⟨δ, δ_gt_0, conv⟩ := conv ε ε_gt_0

    have x_conv := x.conv δ δ_gt_0
    have y_conv := y.conv δ δ_gt_0

    let N := max x_conv.choose y_conv.choose
    exists N
    intro m m_lt_N n n_lt_N

    have x_conv := x_conv.choose_spec
      m (sup_le_iff.mp m_lt_N).left
      n (sup_le_iff.mp n_lt_N).left
    have y_conv := y_conv.choose_spec
      m (sup_le_iff.mp m_lt_N).right
      n (sup_le_iff.mp n_lt_N).right

    exact conv m n x_conv y_conv
⟩

def bounded_by (x : Cauchy) (M : ℚ) := ∀m, |x.seq m| ≤ M

def bounded_by_ge (x : Cauchy) (M : ℚ) (N : ℚ) : M ≤ N → x.bounded_by M → x.bounded_by N := by
  intro N_ge_M x_bounded_by_M
  rw [bounded_by] at *
  grind

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

theorem eq_by_seq {x y : Cauchy} : x = y ↔ x.seq = y.seq := by
  apply Iff.intro
  repeat
    intro seq_eq
    cases x
    cases y
    simp_all

theorem eq_by_forall {x y : Cauchy} : x = y ↔ ∀n, x.seq n = y.seq n := by
  apply Iff.intro
  . intro x_eq_y n
    subst x_eq_y
    rfl
  . intro h
    apply eq_by_seq.mpr
    funext n
    exact (h n)

theorem eq_const {x : Cauchy} {c : ℚ}: (∀i, x.seq i = c) → x = const c := by sorry

instance : Add Cauchy where
  add x y := by
    apply lift₂_single x y (· + ·)

    intro ε ε_gt_0
    exists ε/2
    apply And.intro (div_pos ε_gt_0 rfl)

    intro m n x_conv y_conv

    have := add_lt_add x_conv y_conv
    simp [add_halves] at this
    rw [<-gt_iff_lt] at *

    calc
      ε > |x.seq m - x.seq n| + |y.seq m - y.seq n| := this
      _ ≥ |x.seq m - x.seq n + (y.seq m - y.seq n)| := (abs_add_le _ _).ge
      _ = |x.seq m + y.seq m - (x.seq n + y.seq n)| := by
        rw [@add_sub_assoc', @sub_add_eq_add_sub, tsub_tsub]

theorem add_seq (x y : Cauchy) : (x + y).seq = x.seq + y.seq := by
  rw (occs := .pos [1]) [HAdd.hAdd, instHAdd, Add.add, instAdd]
  unfold lift₂_single
  simp_all

theorem const_add (a b : ℚ) : const (a + b) = const a + const b := by rfl

instance : Zero Cauchy where
  zero := const 0

@[simp]
theorem seq_zero : seq 0 = 0 := neg_eq_zero.mp rfl

@[simp]
theorem zero_def : const 0 = 0 := by exact eq_by_seq.mpr rfl

instance : Neg Cauchy where
  neg x := by
    apply x.lift (- ·)
    intro ε ε_gt_0
    exists ε
    apply And.intro ε_gt_0
    intro m n x_conv
    rw [Neg.neg, Sequence.instNeg, <-abs_neg]
    simp
    rw [Rat.add_comm, ← Rat.sub_eq_add_neg]
    exact x_conv

theorem neg_seq (x : Cauchy) : (-x).seq = -x.seq := by
  rw (occs := .pos [1]) [Neg.neg, instNeg]
  unfold lift
  simp

theorem const_neg (a : ℚ) : const (-a) = -const a := by rfl

--
instance : Sub Cauchy where
  sub x y := x + (-y)

theorem sub_seq (x y : Cauchy) : (x - y).seq = x.seq - y.seq := by
  sorry

instance : Mul Cauchy where
    mul x y := by
      apply lift₂_single x y (· * ·)

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

      exists δ
      apply And.intro δ_gt_0

      intro m n x_conv y_conv
      rw [<-gt_iff_lt] at *

      calc
      ε > ε/4 + ε/4 := by grind_linarith
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
      _ = |(x.seq * y.seq) m - (x.seq * y.seq) n| := by simp [Sequence.mul_distrib]

theorem mul_seq (x y : Cauchy) : (x * y).seq = x.seq * y.seq := by
  rw (occs := .pos [1]) [HMul.hMul, instHMul, Mul.mul, instMul]
  unfold lift₂_single
  simp_all

theorem const_mul (a b : ℚ) : const (a * b) = const a * const b := by rfl

instance : One Cauchy where
    one := const 1

theorem one_def : const 1 = 1 := by exact eq_by_seq.mpr rfl

@[simp]
theorem one_seq : seq 1 = Sequence.const 1 := by rfl

instance : CommRing Cauchy where
  add_assoc x y z := by
    rw [eq_by_seq]
    exact add_assoc _ _ _

  zero_add x := by
    rw [eq_by_seq]
    exact zero_add _

  add_zero x := by
    rw [eq_by_seq]
    exact add_zero _

  nsmul s x := const s * x

  nsmul_zero x := by
    simp [eq_by_seq, mul_seq]

  nsmul_succ n x := by
    simp [const_add, eq_by_seq, mul_seq, add_seq, add_mul]

  add_comm x y := by
    rw [eq_by_seq]
    exact add_comm _ _

  left_distrib x y z := by
    rw [eq_by_seq]
    exact left_distrib _ _ _

  right_distrib x y z := by
    rw [eq_by_seq]
    exact right_distrib _ _ _

  zero_mul x := by
      rw [eq_by_seq]
      exact zero_mul _

  mul_zero x := by
      rw [eq_by_seq]
      exact mul_zero _

  mul_assoc x y z := by
      rw [eq_by_seq]
      exact mul_assoc _ _ _

  one_mul x := by
      rw [eq_by_seq]
      exact one_mul _

  mul_one x := by
      rw [eq_by_seq]
      exact mul_one _

  zsmul z x := const z * x

  zsmul_zero' x := by
      simp [eq_by_seq, mul_seq]

  zsmul_succ' z x := by
      simp [const_add, eq_by_seq, mul_seq, add_seq, add_mul]

  zsmul_neg' z x := by
      simp [const_add, const_neg, eq_by_seq, add_seq, neg_seq, mul_seq]
      grind

  neg_add_cancel x := by
    rw [eq_by_seq]
    exact neg_add_cancel _

  mul_comm x y := by
    rw [eq_by_seq]
    exact mul_comm _ _

abbrev eqv_zero (x : Cauchy) := x.seq.limit 0

theorem nz_gt_zero (x : Cauchy) (x_nz : ¬x.eqv_zero) : ∃N, ∃m > 0, ∀n ≥ N, |x.seq n| ≥ m := by
  sorry

instance : Setoid Cauchy where
  r x y := eqv_zero (x - y)
  iseqv := by
    apply Equivalence.mk

    case refl =>
      intro x ε ε_gt_0
      exists 1
      intro n n_gt_1
      simp
      exact ε_gt_0

    case symm =>
      intro x y h
      rw [eqv_zero, <-Sequence.neg_limit_zero]
      simpa [<-neg_seq] using h

    case trans =>
        -- TODO figure out how use lift
        intro x y z x_eqv_y y_eqv_z ε ε_gt_0

        have x_eqv_y := x_eqv_y (ε/2) (div_pos ε_gt_0 rfl)
        have y_eqv_z := y_eqv_z (ε/2) (div_pos ε_gt_0 rfl)

        let N := max x_eqv_y.choose y_eqv_z.choose
        exists N
        intro n n_gt_N

        have x_eqv_y := x_eqv_y.choose_spec n (sup_le_iff.mp n_gt_N).left
        have y_eqv_z := y_eqv_z.choose_spec n (sup_le_iff.mp n_gt_N).right

        have := add_lt_add x_eqv_y y_eqv_z
        simp [add_halves] at this
        rw [<-gt_iff_lt] at *
        simp [-gt_iff_lt]
        calc
            ε > |x.seq n - y.seq n| + |y.seq n - z.seq n| := sorry
            _ ≥ |x.seq n - y.seq n + (y.seq n - z.seq n)| := by grind
            _ ≥ |x.seq n - z.seq n| := by simp
            _ = |(x - z).seq n| := by sorry

def equiv_iff (x y : Cauchy) : (∀ε > 0, ∃N, ∀n ≥ N, |x.seq n - y.seq n| < ε) ↔ (x ≈ y) := by
  rw [HasEquiv.Equiv, instHasEquivOfSetoid, instSetoid]
  simp [eqv_zero, Sequence.limit]
  simp [sub_seq, Sequence.sub_distrib]

def inv_exists (x : Cauchy) (x_nz : ¬x.eqv_zero) : ∃y : Cauchy, x * y ≈ 1 := by
  let ⟨N, m, m_gt_0, h_m⟩ := nz_gt_zero x x_nz

  let y_seq : Sequence ℚ := fun i ↦ if i ≥ N then (x.seq i)⁻¹ else 0
  let y : Cauchy := ⟨y_seq, ?_⟩
  . exists y

    intro ε ε_gt_0
    exists N
    intro i i_ge_N
    subst y

    simp [*, sub_seq, mul_seq, Sequence.sub_distrib, Sequence.mul_distrib, y_seq]

    have : x.seq i ≠ 0 := by grind

    simpa [Rat.mul_inv_cancel _ this] using ε_gt_0

  . intro ε ε_gt_0
    have h_m2 : m^2 > 0 := Rat.pow_pos m_gt_0
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

noncomputable instance : Inv Cauchy where
  inv x := by
    by_cases x.eqv_zero
    case pos _ => exact 0
    case neg h_x => exact Classical.choose (x.inv_exists h_x)

-- EQUIVS TODO

theorem add_eqv {x₁ y₁ x₂ y₂ : Cauchy} : x₁ ≈ x₂ → y₁ ≈ y₂ → x₁+y₁ ≈ x₂+y₂ := by
  rw [HasEquiv.Equiv, instHasEquivOfSetoid, instSetoid]
  simp [-gt_iff_lt]
  intro x₁_eqv_x₂ y₁_eqv_y₂ ε ε_gt_0

  let δ := ε/2
  have δ_gt_0 : δ > 0 := sorry

  have ⟨N, x₁_eqv_x₂⟩ := x₁_eqv_x₂ δ δ_gt_0
  have ⟨N, y₁_eqv_y₂⟩ := y₁_eqv_y₂ δ δ_gt_0
  sorry

theorem neg_eqv {x y : Cauchy} : x ≈ y → (-x) ≈ (-y) := by
  sorry

theorem mul_eqv {x₁ y₁ x₂ y₂ : Cauchy} : x₁ ≈ x₂ → y₁ ≈ y₂ → x₁*y₁ ≈ x₂*y₂ := by
  sorry

theorem sub_eqv {x₁ y₁ x₂ y₂ : Cauchy} : x₁ ≈ x₂ → y₁ ≈ y₂ → x₁-y₁ ≈ x₂-y₂ := by
  sorry

theorem pow_eqv {x y : Cauchy} {n : ℕ} : x ≈ y → x ^ n ≈ y ^ n := by sorry

theorem smul_eqv {x y : Cauchy} (z : ℤ) : x ≈ y → z • x ≈ z • y := by sorry

theorem inv_eqv {x y : Cauchy} : x ≈ y → x⁻¹ ≈ y⁻¹ := by
  sorry

theorem one_neqv_zero : ¬(1 : Cauchy) ≈ 0 := by
  intro h
  rw [HasEquiv.Equiv, instHasEquivOfSetoid, instSetoid] at h
  simp [eqv_zero] at h
  apply Sequence.limit_not_const 1 0 (by norm_num) h

end Cauchy
