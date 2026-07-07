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

open Sequence (converges cauchy bounded monotone map₀ map map₂ )


structure CauchySequence where
  seq : Sequence ℚ
  cauchy : cauchy seq

abbrev CauSeq := CauchySequence

namespace Cauchy

section basic

-- TODO simplify
theorem seq_ext {x y : CauSeq} : x.seq = y.seq → x = y := by
  intro h
  cases x
  subst h
  rfl

theorem bounded (x : CauSeq) : x.seq.bounded := Sequence.cauchy_bounded x.cauchy


end basic

section lifts

abbrev lifts₀ (f : 𝕊 ℚ) := cauchy f

def lift₀ {f : 𝕊 ℚ} (h_f : cauchy f) : CauSeq := ⟨f, h_f⟩

abbrev const (a : ℚ) : CauSeq := by
  apply @lift₀ (map₀ a)
  intro ε ε_gt_0
  exists 0
  simp
  grind

abbrev lifts (f : 𝕊 ℚ → 𝕊 ℚ) := ∀{x : CauSeq}, cauchy (f x.seq)

def lift {f : 𝕊 ℚ → 𝕊 ℚ} (h_f : lifts f) (x : CauSeq) : CauSeq := ⟨f x.seq, h_f⟩

abbrev lifts₂ (f : 𝕊 ℚ → 𝕊 ℚ → 𝕊 ℚ) := ∀{x y : CauSeq}, cauchy (f x.seq y.seq)

def lift₂ {f : 𝕊 ℚ → 𝕊 ℚ → 𝕊 ℚ} (h_f : lifts₂ f) (x y : CauSeq) : CauSeq := ⟨f x.seq y.seq, h_f⟩


@[simp]
theorem lift₀_seq {f : 𝕊 ℚ} (h_f : lifts₀ f) : (@lift₀ f h_f).seq = f := rfl

@[simp]
theorem lift_seq {f : 𝕊 ℚ → 𝕊 ℚ} (h_f : lifts f) (x : CauSeq) : (@lift f h_f x).seq = f x.seq := rfl

@[simp]
theorem lift₂_seq {f : 𝕊 ℚ → 𝕊 ℚ → 𝕊 ℚ} (h_f : lifts₂ f) (x y : CauSeq) : (@lift₂ f h_f x y).seq = f x.seq y.seq := rfl

theorem lifts_by (f : 𝕊 ℚ → 𝕊 ℚ)
  (h :
    ∀x : CauSeq,
    ∀ε > 0,
    ∃δ > 0,
    ∀ i j,
    |x.seq i - x.seq j| < δ →
    |f x.seq i - f x.seq j| < ε
  ) : lifts f := by
  intro x ε ε_gt_0
  let ⟨δ, δ_gt_0, h⟩ := h x ε ε_gt_0
  let ⟨N, h_x⟩ := x.cauchy δ δ_gt_0
  exists N
  grind

theorem lifts₂_by (f : 𝕊 ℚ → 𝕊 ℚ → 𝕊 ℚ)
  (h :
    ∀x y : CauSeq,
    ∀ε > 0,
    ∃δ > 0,
    ∀ i j,
    |x.seq i - x.seq j| < δ →
    |y.seq i - y.seq j| < δ →
    |f x.seq y.seq i - f x.seq y.seq j| < ε
  ) : lifts₂ f := by
  intro x y ε ε_gt_0
  let ⟨δ, δ_gt_0, h⟩ := h x y ε ε_gt_0
  let ⟨N₁, h_x⟩ := x.cauchy δ δ_gt_0
  let ⟨N₂, h_x⟩ := y.cauchy δ δ_gt_0
  let N := max N₁ N₂
  exists N
  grind

end lifts

section arithmetic

theorem add_lifts : lifts₂ (·+·) := by
  apply lifts₂_by
  intro x y ε ε_gt_0
  refine ⟨ε/2, by grind, ?_⟩
  simp
  grind

instance : Add CauSeq := ⟨@lift₂ (·+·) add_lifts⟩

@[simp]
theorem add_seq (x y : CauSeq) : (x + y).seq = x.seq + y.seq := by rfl

theorem const_add (a b : ℚ) : const (a + b) = const a + const b := by rfl

instance : Zero CauSeq := ⟨const 0⟩

@[simp]
theorem zero_seq : (0 : CauSeq).seq = 0 := by rfl

theorem neg_lifts : lifts (-·) := by
  apply lifts_by
  intro x ε ε_gt_0
  refine ⟨ε, ε_gt_0, ?_⟩
  simp
  grind

instance : Neg CauSeq := ⟨@lift (-·) neg_lifts⟩

@[simp]
theorem neg_seq (x : CauSeq) : (-x).seq = -x.seq := by rfl

theorem mul_lifts : lifts₂ (·*·) := by
  apply lifts₂_by
  intro x y

  let ⟨X, h_X⟩ := bounded x
  let ⟨Y, h_Y⟩ := bounded y
  let M := max X Y
  have ⟨M_pos, h_Mx⟩ : x.seq.bounded_by M := Sequence.bounded_by_ge h_X (by grind)
  have ⟨M_pos, h_My⟩ : y.seq.bounded_by M := Sequence.bounded_by_ge h_Y (by grind)

  intro ε ε_gt_0

  let δ := ε/(4*M)
  have δ_pos : δ > 0 := div_pos (by grind) (by grind [h_X.left])
  refine ⟨δ, δ_pos, ?_⟩

  intro i j h_x h_y

  calc
    ε > ε/4 + ε/4 := by grind
    _ = M * (ε/(4*M)) + (ε/(4*M)) * M := by grind
    _ ≥ M * |y.seq i - y.seq j| + |x.seq i - x.seq j| * M := by gcongr
    _ ≥ |x.seq i| * |y.seq i - y.seq j| + |x.seq i - x.seq j| * |y.seq j| := by gcongr <;> grind
    _ = |x.seq i * (y.seq i - y.seq j)| + |(x.seq i - x.seq j) * y.seq j| := by simp
    _ ≥ |x.seq i * (y.seq i - y.seq j) + (x.seq i - x.seq j) * y.seq j| := abs_add_le _ _
    _ = |(x.seq i * y.seq i) - (x.seq j * y.seq j)| := by grind

instance : Mul CauSeq := ⟨@lift₂ (·*·) mul_lifts⟩

@[simp]
theorem mul_seq (x y : CauSeq) : (x * y).seq = x.seq * y.seq := by rfl

instance : One CauSeq := ⟨const 1⟩

@[simp]
theorem one_seq : (1 : CauSeq).seq = 1 := by rfl

instance : CommRing CauSeq where
  add_assoc x y z := by
    apply seq_ext
    grind [add_seq]

  zero_add x := by
    apply seq_ext
    simp [add_seq]

  add_zero x := by
    apply seq_ext
    simp [add_seq]

  add_comm x y := by
    apply seq_ext
    grind [add_seq]

  neg_add_cancel x := by
    apply seq_ext
    simp [add_seq, neg_seq]

  left_distrib x y z := by
    apply seq_ext
    grind [add_seq, mul_seq]

  right_distrib x y z := by
    apply seq_ext
    grind [add_seq, mul_seq]

  zero_mul x := by
    apply seq_ext
    simp [mul_seq]

  mul_zero x := by
    apply seq_ext
    simp [mul_seq]

  mul_assoc x y z := by
    apply seq_ext
    grind [mul_seq]

  one_mul x := by
    apply seq_ext
    simp [mul_seq]

  mul_one x := by
    apply seq_ext
    simp [mul_seq]

  mul_comm x y := by
    apply seq_ext
    grind [mul_seq]

  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp]
theorem sub_seq (x y : CauSeq) : (x - y).seq= x.seq - y.seq := by
  simp [sub_eq_add_neg]

end arithmetic

section equivalence

variable {x x₁ x₂ y y₁ y₂ : CauSeq}

instance instSetoid : Setoid CauSeq where
  r x y := (x - y).seq ⟶ 0
  iseqv := by
    apply Equivalence.mk

    case refl =>
      intro x ε ε_gt_0
      exists 0
      simp
      grind

    case symm =>
      intro x y h
      simp [Sequence.converges_to, sub_seq] at h
      simpa [Sequence.converges_to, sub_seq, abs_sub_comm]

    case trans =>
        intro x y z x_eqv_y y_eqv_z ε ε_gt_0

        have ⟨N₁, x_eqv_y⟩ := x_eqv_y (ε/2) (div_pos ε_gt_0 rfl)
        have ⟨N₂, y_eqv_z⟩ := y_eqv_z (ε/2) (div_pos ε_gt_0 rfl)

        let N := max N₁ N₂
        exists N
        intro n n_ge_N
        simp [sub_seq] at *
        grind

theorem eqv_def : x ≈ y ↔ ((x - y).seq ⟶ 0) := Eq.to_iff rfl

theorem eqv_zero : x ≈ 0 ↔ x.seq ⟶ 0 := by simp [eqv_def]

theorem eqv_iff : x ≈ y ↔ ∀ε > 0, ∃N, ∀i > N, |x.seq i - y.seq i| < ε := by
  unfold HasEquiv.Equiv instHasEquivOfSetoid instSetoid
  simp [Sequence.converges_to]

abbrev interleave (x_eqv_y : x ≈ y) : CauSeq := by
  let s : Sequence ℚ := fun i ↦ if Even i then x.seq (i/2) else y.seq (i/2)
  refine ⟨s, ?_⟩
  intro ε ε_gt_0
  let ⟨N₁, h_x⟩ := x.cauchy (ε/2) (by grind)
  let ⟨N₂, h_y⟩ := y.cauchy (ε/2) (by grind)
  let ⟨N₃, eqv⟩ := x_eqv_y (ε/2) (by grind)
  simp [] at eqv
  let N := 2 * (max N₁ (max N₂ N₃) + 1)
  exists N
  intro i i_gt_N j j_gt_N
  have h_x := h_x (i/2) (by grind) (j/2) (by grind)
  have h_y := h_y (i/2) (by grind) (j/2) (by grind)

  unfold s
  split <;> split <;> grind

theorem add_eqv : x₁ ≈ x₂ → y₁ ≈ y₂ → x₁+y₁ ≈ x₂+y₂ := by
  simp [eqv_def]
  intro h_x h_y
  rw [add_sub_add_comm, show (0 : ℚ) = 0 + 0 by simp]

  exact Sequence.add_converges h_x h_y

theorem neg_eqv : x ≈ y →  (-x) ≈ (-y) := by
  simp [eqv_def]
  intro h
  rw [
    show -x.seq + y.seq = -(x.seq - y.seq) by grind,
    show (0 : ℚ) = -0 by simp
  ]
  exact Sequence.neg_converges h

theorem mul_eqv : x₁ ≈ x₂ → y₁ ≈ y₂ → x₁*y₁ ≈ x₂*y₂ := by
  simp [eqv_def]
  intro h_x h_y
  rw [
    show x₁.seq*y₁.seq - x₂.seq*y₂.seq = x₁.seq*(y₁.seq - y₂.seq) + (x₁.seq - x₂.seq)*y₂.seq by grind,
    show (0 : ℚ) = 0 + 0 by simp
  ]
  apply Sequence.add_converges
  . exact Sequence.bounded_mul_eqv_zero_eqv_zero (bounded x₁) h_y
  . exact Sequence.eqv_zero_mul_bounded_eqv_zero h_x (bounded y₂)

theorem exists_inv (x_nz : ¬x ≈ 0) : ∃y, x * y ≈ 1 := by
  let : ¬x.seq ⟶ 0 := fun h ↦ x_nz (eqv_zero.mpr h)
  let ⟨m, m_pos, Nm, h_m⟩ := Sequence.cauchy_neqv_zero_gt_zero x.cauchy (by grind)

  let y_seq : Sequence ℚ := fun i ↦ if i ≥ Nm then (x.seq i)⁻¹ else 0

  have : cauchy y_seq := by
    have : m^2 > 0 := Rat.pow_pos m_pos

    intro ε ε_gt_0

    let δ := m^2 * ε / 2
    have δ_pos : δ > 0 := by grind [Rat.mul_pos_iff_of_pos_left]
    let ⟨Nx, h_x⟩ := x.cauchy δ δ_pos

    let N := max Nm Nx
    exists N
    intro i i_gt_N j j_gt_N

    have h_x := h_x i (by grind) j (by grind)
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
  exists Nm
  intro i i_ge_N
  simp
  grind

noncomputable instance : Inv CauSeq where
  inv x := by
    by_cases x ≈ 0
    case pos _ => exact 0
    case neg h_x => exact (exists_inv h_x).choose

theorem mul_inv_eqv_cancel (x_nz : ¬x ≈ 0) : x * x⁻¹ ≈ 1 := by
  simp [Inv.inv, x_nz]
  grind

theorem one_neqv_zero : ¬(1 : CauSeq) ≈ 0 := by
  simp [eqv_iff]
  refine ⟨1, rfl, ?_⟩
  intro N
  refine ⟨⟨N+1, by grind⟩, ?_⟩
  simp

theorem inv_eqv_zero : x ≈ 0 → x⁻¹ = 0 := by
  intro x_eqv_0
  simp [Inv.inv]
  intro h
  contradiction

theorem eqv_inv_iff (y_nz : ¬y ≈ 0) : x ≈ y⁻¹ ↔ x * y ≈ 1 := by
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

theorem inv_eqv : x ≈ y → x⁻¹ ≈ y⁻¹ := by
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

end Cauchy
