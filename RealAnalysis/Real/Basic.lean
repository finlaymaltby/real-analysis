import RealAnalysis.Real.Cauchy

structure Real where
    cauchy : Cauchy.Completion

notation "ℝ" => Real

namespace Real

abbrev cauchy_mk (cauchy : Cauchy) : ℝ := ⟨Quotient.mk Cauchy.instSetoid cauchy⟩

private def eq_iff : ∀ {x y : ℝ}, x = y ↔ x.cauchy = y.cauchy
    | ⟨a⟩, ⟨b⟩ => by rw [mk.injEq]

private def lift (f : Cauchy → Cauchy) (h_f : ∀ (a b : Cauchy), a ≈ b → f a ≈ f b) (x : ℝ) := by
    refine Quotient.lift (cauchy_mk ∘ f) ?_ x.cauchy
    simp [eq_iff, Quotient.eq_iff_equiv]
    exact h_f

private def lift₂  (f : Cauchy → Cauchy → Cauchy)
    (h_f : ∀ (a₁ b₁ a₂ b₂ : Cauchy), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ ≈ f a₂ b₂) (x y : ℝ) := by
        refine Quotient.lift₂ (λ a b ↦ cauchy_mk (f a b)) ?_ x.cauchy y.cauchy
        simp [eq_iff, Quotient.eq_iff_equiv]
        exact h_f

namespace Coe

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

instance : Add ℝ where
    add := lift₂ (· + ·) @Cauchy.add_eqv

theorem cauchy_add {x y : ℝ} : cauchy (x + y) = cauchy x + cauchy y := sorry

instance : Zero ℝ where
    zero := mk 0

theorem cauchy_zero : cauchy 0 = 0 := sorry

instance : Neg ℝ where
    neg := lift (- ·) @Cauchy.neg_eqv

theorem cauchy_neg {x : ℝ} : cauchy (-x) = - cauchy x := sorry

instance : Mul ℝ where
     mul := lift₂ (· * ·) @Cauchy.mul_eqv

theorem cauchy_mul {x y : ℝ} : cauchy (x * y) = cauchy x * cauchy y := sorry

instance : One ℝ where
    one := mk 1

theorem cauchy_one : cauchy 1 = 1 := sorry

instance : NatCast ℝ where
    natCast n := ⟨n⟩

theorem cauchy_natCast {n : ℕ}: cauchy (NatCast.natCast n) = NatCast.natCast n := sorry

instance : CommRing ℝ where
    natCast n := mk n
    intCast z := mk z
    npow := npowRec
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_zero a := by apply eq_iff.mpr; simp [cauchy_add, cauchy_zero]
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
    natCast_zero := by apply eq_iff.mpr; simp [cauchy_zero]
    natCast_succ n := by apply eq_iff.mpr; simp [cauchy_one, cauchy_add]
    intCast_negSucc z := by apply eq_iff.mpr; simp [cauchy_neg, cauchy_natCast]

instance : Inv ℝ where
    inv := lift (Inv.inv) @Cauchy.inv_eqv

instance : Field ℝ where



#eval 1.0/0.0

end Real
