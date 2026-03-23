import RealAnalysis.Real.Cauchy

open Cauchy

abbrev Completion := Quotient Cauchy.instSetoid

instance : Add Completion := ⟨Quotient.map₂ (· + ·) (fun _ _ h_a _ _ h_b => add_eqv h_a h_b)⟩

instance : Zero Completion := ⟨Quotient.mk' 0⟩

instance : Neg Completion := ⟨Quotient.map (- ·) (fun _ _ h => neg_eqv h)⟩

instance : Mul Completion := ⟨Quotient.map₂ (· * ·) (fun _ _ h_a _ _ h_b => mul_eqv h_a h_b)⟩

instance : One Completion := ⟨Quotient.mk' 1⟩

instance : IntCast Completion := ⟨Quotient.mk' ∘ IntCast.intCast⟩

instance : NatCast Completion := ⟨Quotient.mk' ∘ NatCast.natCast⟩

instance : Pow Completion ℕ where
  pow a n := Quotient.map (· ^ n) (fun _ _ h => pow_eqv h) a

instance : SMul ℤ Completion where
  smul z := Quotient.map (z • ·) (fun _ _ h => smul_eqv z h)

instance : SMul ℕ Completion where
  smul n := Quotient.map ((n : ℤ) • ·) (fun _ _ h => smul_eqv n h)

instance : Sub Completion :=
  ⟨Quotient.map₂ (· - ·) (fun _ _ h_a _ _ h_b => sub_eqv h_a h_b)⟩

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

instance : Field Completion where
  inv := Quotient.map (Inv.inv) @inv_eqv
  mul_inv_cancel a a_nz := by
    apply mul_inv

  exists_pair_ne := by
    exists Quotient.mk' 1, Quotient.mk' 0
    intro h
    rw [Quotient.eq'] at h
    apply one_neqv_zero h
