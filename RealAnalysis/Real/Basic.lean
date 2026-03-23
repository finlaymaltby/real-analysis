import RealAnalysis.Real.Cauchy
import RealAnalysis.Real.Completion

structure Real where
    inner : Completion

notation "ℝ" => Real

namespace Real

private abbrev cauchy_mk (cauchy : Cauchy) : ℝ := ⟨Quotient.mk Cauchy.instSetoid cauchy⟩

private def eq_iff : ∀ {x y : ℝ}, x = y ↔ x.inner = y.inner
    | ⟨a⟩, ⟨b⟩ => by rw [mk.injEq]

private def lift (f : Completion → Completion) (x : ℝ) : ℝ := ⟨f x.inner⟩

private def lift₂  (f : Completion → Completion → Completion) (x y : ℝ) : ℝ := ⟨f x.inner y.inner⟩

@[simp]
theorem lift_cauchy {x : ℝ} : (lift f x).inner = f x.inner := rfl

section Coe

instance : Coe ℚ ℝ where
    coe x := ⟨Quotient.mk' $ Cauchy.const x⟩

instance : Coe ℕ ℝ where
    coe n := ↑(n : ℚ)

instance : Coe ℤ ℝ where
    coe z := ↑(z : ℚ)

instance (n : ℕ) : OfNat ℝ n := ⟨↑n⟩

instance : OfScientific ℝ where
    ofScientific n b e := ↑(Rat.ofScientific n b e)

end Coe

instance : Add ℝ := ⟨lift₂ (· + ·)⟩

theorem cauchy_add {x y : ℝ} : inner (x + y) = inner x + inner y := sorry

instance : Zero ℝ := ⟨0⟩

theorem cauchy_zero : inner 0 = 0 := sorry

instance : Neg ℝ := ⟨lift (- ·)⟩

theorem cauchy_neg {x : ℝ} : inner (-x) = - inner x := sorry

instance : Mul ℝ := ⟨lift₂ (· * ·)⟩

theorem cauchy_mul {x y : ℝ} : inner (x * y) = inner x * inner y := sorry

instance : One ℝ := ⟨1⟩

theorem cauchy_one : inner 1 = 1 := sorry

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
    inv := lift (Inv.inv)
    mul_inv_cancel a a_neq_0 := by
        apply eq_iff.mpr

        simp [cauchy_mul, cauchy_one, lift_cauchy]
        refine Field.mul_inv_cancel a.inner ?_
        exact ne_of_apply_ne mk a_neq_0
    inv_zero := by simp [eq_iff]; exact inv_zero

    exists_pair_ne := by exists ⟨1⟩, ⟨0⟩; simp

    nnqsmul := _
    qsmul := _



end Real
