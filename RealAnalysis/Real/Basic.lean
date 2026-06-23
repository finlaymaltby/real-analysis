import RealAnalysis.Real.Cauchy
import RealAnalysis.Real.Completion

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Defs.Basic


structure Real where
  cauchy : Completion

notation "ℝ" => Real

namespace Real

section basic

private def eq_iff : ∀ {x y : ℝ}, x = y ↔ x.cauchy = y.cauchy
  | ⟨a⟩, ⟨b⟩ => by rw [mk.injEq]

private def lift (f : Completion → α) (x : ℝ) : α := f x.cauchy
private def lift₂ (f : Completion → Completion → α) (x y : ℝ) : α := f x.cauchy y.cauchy


private def map (f : Completion → Completion) (x : ℝ) : ℝ := ⟨f x.cauchy⟩
private def map₂ (f : Completion → Completion → Completion) (x y : ℝ) : ℝ := ⟨f x.cauchy y.cauchy⟩
@[simp]
theorem map_cauchy (x : ℝ) : (map f x).cauchy = f x.cauchy := rfl
@[simp]
theorem map₂_cauchy (x y : ℝ) : (map₂ f x y).cauchy = f x.cauchy y.cauchy := rfl

instance : Coe ℚ ℝ where
  coe x := ⟨Quotient.mk' $ Cauchy.const x⟩

instance : Coe ℕ ℝ where
  coe n := ↑(n : ℚ)

instance : Coe ℤ ℝ where
  coe z := ↑(z : ℚ)

instance (n : ℕ) : OfNat ℝ n := ⟨↑n⟩

instance : OfScientific ℝ where
  ofScientific n b e := ↑(Rat.ofScientific n b e)

end basic

section arithmetic

instance : Add ℝ := ⟨map₂ (· + ·)⟩
theorem cauchy_add (x y : ℝ) : cauchy (x + y) = cauchy x + cauchy y := rfl

instance : Zero ℝ := ⟨0⟩
theorem cauchy_zero : cauchy 0 = 0 := rfl

instance : Neg ℝ := ⟨map (- ·)⟩
theorem cauchy_neg (x : ℝ) : cauchy (-x) = - cauchy x := rfl

instance : Mul ℝ := ⟨map₂ (· * ·)⟩
theorem cauchy_mul (x y : ℝ) : cauchy (x * y) = cauchy x * cauchy y := rfl

instance : One ℝ := ⟨1⟩
theorem cauchy_one : cauchy 1 = 1 := rfl

instance : CommRing ℝ where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_zero a := by apply eq_iff.mpr; simp [cauchy_zero, cauchy_add]
  zero_add a := by apply eq_iff.mpr; simp [cauchy_add, cauchy_zero]
  add_comm a b := by apply eq_iff.mpr; simp only [cauchy_add, add_comm]
  add_assoc a b c := by apply eq_iff.mpr; simp only [cauchy_add, add_assoc]
  mul_zero a := by apply eq_iff.mpr; simp [cauchy_mul, cauchy_zero]
  zero_mul a := by apply eq_iff.mpr; simp [cauchy_mul, cauchy_zero]
  mul_one a := by apply eq_iff.mpr; simp [cauchy_mul, cauchy_one]
  one_mul a := by apply eq_iff.mpr; simp [cauchy_mul, cauchy_one]
  mul_comm a b := by apply eq_iff.mpr; simp only [cauchy_mul, mul_comm]
  mul_assoc a b c := by apply eq_iff.mpr; simp only [cauchy_mul, mul_assoc]
  left_distrib a b c := by apply eq_iff.mpr; simp only [cauchy_add, cauchy_mul, mul_add]
  right_distrib a b c := by apply eq_iff.mpr; simp only [cauchy_add, cauchy_mul, add_mul]
  neg_add_cancel a := by apply eq_iff.mpr; simp [cauchy_add, cauchy_neg, cauchy_zero]

noncomputable instance : Field ℝ where
  inv := map (Inv.inv)
  inv_zero := by simp [eq_iff]; exact inv_zero
  mul_inv_cancel a a_neq_0 := by
    apply eq_iff.mpr

    simp [cauchy_mul, cauchy_one, map_cauchy]
    refine Field.mul_inv_cancel a.cauchy ?_
    exact ne_of_apply_ne mk a_neq_0

  exists_pair_ne := by exists ⟨1⟩, ⟨0⟩; simp
  nnqsmul := _
  qsmul := _

end arithmetic

section order

def lt := lift₂ LT.lt
instance : LT ℝ := ⟨lt⟩
def le := lift₂ LE.le
instance : LE ℝ := ⟨le⟩
def le_iff :  ∀ {x y : ℝ}, x ≤ y ↔ x.cauchy ≤ y.cauchy := by
  intro x y
  constructor <;> solve_by_elim

instance : PartialOrder ℝ where
  le_refl a := le_refl a.cauchy
  le_trans a b c hab hbc := by
    apply le_iff.mpr
    exact le_trans (le_iff.mp hab) (le_iff.mp hbc)
  lt_iff_le_not_ge a b := sorry
  le_antisymm := sorry

instance : DistribLattice ℝ := sorry

instance : Archimedean ℝ where
  arch x y y_pos := by
    sorry

instance : LinearOrder ℝ := by sorry


-- Topology
-- maybe no metric space, requires lean4 ℝ
-- instance : MetricSpace ℝ := sorry

-- instance : CompleteSpace ℝ := sorry

-- instance : NormedField ℝ := sorry

end order

end Real

namespace Sequence

theorem cauchy_converges {x : Sequence ℝ} : x.cauchy → x.converges := by sorry


end Sequence
