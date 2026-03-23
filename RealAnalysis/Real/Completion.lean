import RealAnalysis.Real.Cauchy

abbrev Completion := Quotient Cauchy.instSetoid

namespace Completion

instance : Add Completion := ⟨Quotient.map₂ (· + ·) (fun _ _ h_a _ _ h_b => Cauchy.add_eqv h_a h_b)⟩

instance : Zero Completion := ⟨⟦0⟧⟩

def zero_def : (0 : Completion) = ⟦0⟧ := by rfl

instance : Neg Completion := ⟨Quotient.map (- ·) (fun _ _ h => Cauchy.neg_eqv h)⟩

instance : Mul Completion := ⟨Quotient.map₂ (· * ·) (fun _ _ h_a _ _ h_b => Cauchy.mul_eqv h_a h_b)⟩

theorem mk_mul {x y : Cauchy} : ⟦x⟧ * ⟦y⟧ = (⟦x * y⟧ : Completion) := by
  rw [HMul.hMul, instHMul]
  simp [Mul.mul]

instance : One Completion := ⟨⟦1⟧⟩

instance : IntCast Completion := ⟨Quotient.mk' ∘ IntCast.intCast⟩

instance : NatCast Completion := ⟨Quotient.mk' ∘ NatCast.natCast⟩

instance : Pow Completion ℕ where
  pow a n := Quotient.map (· ^ n) (fun _ _ h => Cauchy.pow_eqv h) a

instance : SMul ℤ Completion where
  smul z := Quotient.map (z • ·) (fun _ _ h => Cauchy.smul_eqv z h)

instance : SMul ℕ Completion where
  smul n := Quotient.map ((n : ℤ) • ·) (fun _ _ h => Cauchy.smul_eqv n h)

instance : Sub Completion :=
  ⟨Quotient.map₂ (· - ·) (fun _ _ h_a _ _ h_b => Cauchy.sub_eqv h_a h_b)⟩

instance : CommRing Completion := fast_instance% by
  apply Function.Surjective.commRing Quotient.mk' (Quotient.mk'_surjective)
  . rfl
  . rfl
  . exact (fun a b => rfl)
  . exact (fun a b => rfl)
  . exact (fun a => rfl)
  . exact (fun a b => rfl)
  . intro n x
    apply Quotient.eq_iff_equiv.mpr
    simpa using Setoid.refl (n * x)
  . intro z x
    apply Quotient.eq_iff_equiv.mpr
    simpa using Setoid.refl (z * x)
  . exact (fun x n => rfl)
  . exact (fun a => rfl)
  . exact (fun a => rfl)

instance : Coe ℚ Completion := ⟨fun q => ⟦↑q⟧⟩

noncomputable instance : Field Completion where
  inv := Quotient.map (Inv.inv) @Cauchy.inv_eqv
  mul_inv_cancel := by
    rw [Quotient.forall]
    intro a a_neq_0
    simp [Quotient.map_mk, mk_mul]

    apply Quotient.eq_iff_equiv.mpr
    apply Cauchy.mul_inv_cancel

    simp [zero_def, Quotient.eq, Cauchy.instSetoid] at a_neq_0
    exact a_neq_0

  inv_zero := by
    simp [zero_def, Quotient.eq_iff_equiv, Inv.inv]
    rw [dite_cond_eq_true (eq_true Cauchy.zero_eqv_zero)]
    exact Setoid.refl 0

  exists_pair_ne := by
    exists Quotient.mk' 1, Quotient.mk' 0
    intro h
    rw [Quotient.eq'] at h
    apply Cauchy.one_neqv_zero h

  nnqsmul := _
  qsmul := _


end Completion
