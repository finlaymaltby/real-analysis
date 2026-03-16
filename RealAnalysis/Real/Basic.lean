import RealAnalysis.Real.Cauchy

structure Real where
    cauchy: Cauchy.Setoid

notation "ℝ" => Real

namespace Real

private def eq_iff : ∀ {x y : ℝ}, x = y ↔ x.cauchy = y.cauchy
    | ⟨a⟩, ⟨b⟩ => by rw [mk.injEq]

private def lift (x : ℝ) (f : Cauchy → Cauchy) (h_f : ∀ (a b : Cauchy), a ≈ b → f a ≈ f b) := by
    refine Quotient.lift (mk ∘ f) ?_ x.cauchy
    simp [eq_iff]
    exact h_f

private def lift₂ (x y : ℝ) (f : Cauchy → Cauchy → Cauchy)
    (h_f : ∀ (a₁ b₁ a₂ b₂ : Cauchy), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ ≈ f a₂ b₂) := by
        refine Quotient.lift₂ (λ a b ↦ mk (f a b)) ?_ x y
        simp [eq_iff]
        exact h_f

namespace Coe

instance : Coe ℚ ℝ where
    coe x := mk x

instance : Coe ℕ ℝ where
    coe n := ↑(n : ℚ)

instance : Coe ℤ ℝ where
    coe z := ↑(z : ℚ)

instance (n : ℕ) : OfNat ℝ n := ⟨↑n⟩

instance : OfScientific ℝ where
    ofScientific n b e := ↑(Rat.ofScientific n b e)

end Coe

instance : Add ℝ where
    add x y := by
        apply lift₂ x y (· + ·)
        exact Cauchy.add_eqv

instance : Zero ℝ where
    zero := mk 0

instance : Neg ℝ where
    neg x := by
        apply lift x (- ·)
        exact Cauchy.neg_eqv

instance : Mul ℝ where
     mul x y := by
        apply lift₂ x y (· * ·)
        exact Cauchy.mul_eqv

instance : One ℝ where
    one := mk 1

instance : CommRing ℝ where
    natCast n := mk n
    intCast z := mk z
    npow := npowRec
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_zero a := by apply eq_iff.mpr; simp [cauchy_add, cauchy_zero]
    zero_add a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
    add_comm a b := by apply ext_cauchy; simp only [cauchy_add, add_comm]
    add_assoc a b c := by apply ext_cauchy; simp only [cauchy_add, add_assoc]
    mul_zero a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
    zero_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
    mul_one a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
    one_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
    mul_comm a b := by apply ext_cauchy; simp only [cauchy_mul, mul_comm]
    mul_assoc a b c := by apply ext_cauchy; simp only [cauchy_mul, mul_assoc]
    left_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, mul_add]
    right_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, add_mul]
    neg_add_cancel a := by apply ext_cauchy; simp [cauchy_add, cauchy_neg, cauchy_zero]
    natCast_zero := by apply ext_cauchy; simp [cauchy_zero]
    natCast_succ n := by apply ext_cauchy; simp [cauchy_one, cauchy_add]
    intCast_negSucc z := by apply ext_cauchy; simp [cauchy_neg, cauchy_natCast]
instance : Field ℝ where


end Real
