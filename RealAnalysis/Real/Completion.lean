import RealAnalysis.Real.Cauchy

abbrev Completion := Quotient Cauchy.instSetoid

namespace Completion

instance : Add Completion := ⟨Quotient.map₂ (· + ·) (fun _ _ h_a _ _ h_b => Cauchy.add_eqv h_a h_b)⟩

theorem mk_add {a b : Cauchy} : ⟦a⟧ + ⟦b⟧ = (⟦a + b⟧ : Completion) := by rfl

instance : Zero Completion := ⟨⟦0⟧⟩

def mk_zero : (0 : Completion) = ⟦0⟧ := by rfl

instance : Neg Completion := ⟨Quotient.map (- ·) (fun _ _ h => Cauchy.neg_eqv h)⟩

theorem mk_neg {a : Cauchy} : -⟦a⟧  = (⟦-a⟧ : Completion) := by rfl

instance : Mul Completion := ⟨Quotient.map₂ (· * ·) (fun _ _ h_a _ _ h_b => Cauchy.mul_eqv h_a h_b)⟩

theorem mk_mul {a b : Cauchy} : ⟦a⟧ * ⟦b⟧ = (⟦a * b⟧ : Completion) := by rfl

instance : One Completion := ⟨⟦1⟧⟩

theorem mk_one : (1 : Completion) = ⟦1⟧ := by rfl

instance : CommRing Completion where
  nsmul := nsmulRec
  zsmul := zsmulRec

  add_zero := by simp [Quotient.forall, mk_add, mk_zero]
  zero_add := by simp [Quotient.forall, mk_add, mk_zero]
  add_comm := by simp [Quotient.forall, mk_add, add_comm]
  add_assoc := by simp [Quotient.forall, mk_add, add_assoc]
  neg_add_cancel := by
    simp [Quotient.forall, mk_add, mk_neg, mk_zero, neg_add_cancel]

  mul_zero := by simp [Quotient.forall, mk_mul, mk_zero]
  zero_mul := by simp [Quotient.forall, mk_mul, mk_zero]
  mul_one := by simp [Quotient.forall, mk_mul, mk_one]
  one_mul := by simp [Quotient.forall, mk_mul, mk_one]
  mul_comm := by simp [Quotient.forall, mk_mul, mul_comm]
  mul_assoc := by simp [Quotient.forall, mk_mul, mul_assoc]

  left_distrib := by simp [Quotient.forall, mk_add, mk_mul, left_distrib]
  right_distrib := by simp [Quotient.forall, mk_add, mk_mul, right_distrib]

noncomputable instance : Field Completion where
  inv := Quotient.map (Inv.inv) @Cauchy.inv_eqv
  mul_inv_cancel := by
    rw [Quotient.forall]
    intro a a_neq_0
    simp [Quotient.map_mk, mk_mul]

    apply Quotient.eq_iff_equiv.mpr
    refine Cauchy.mul_inv_eqv_cancel ?_
    simpa [<-Quotient.eq_iff_equiv]

  inv_zero := by
    simp [mk_zero, Quotient.eq_iff_equiv, Inv.inv]
    rw [dite_cond_eq_true (eq_true (Setoid.refl 0))]
    exact Setoid.refl 0

  exists_pair_ne := by
    exists Quotient.mk' 1, Quotient.mk' 0
    intro h
    rw [Quotient.eq'] at h
    apply Cauchy.one_neqv_zero h

  nnqsmul := _
  qsmul := _



end Completion
