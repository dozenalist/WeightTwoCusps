module

public import Dimension.Gamma_0.Relation

/-! # Two cusp classes at prime level -/

@[expose] public section

noncomputable section

open scoped MatrixGroups
open MulAction

namespace WeightTwoCusps

private theorem prime_cusp_representatives (p : ℕ) [Fact p.Prime] (g : SL(2, ℤ)) :
    (⟦(g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p)⟧ :
      subgroupCusps (CongruenceSubgroup.Gamma0 p)) = ⟦((1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ _)⟧ ∨
    (⟦(g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p)⟧ :
      subgroupCusps (CongruenceSubgroup.Gamma0 p)) = ⟦(ModularGroup.S : SL(2, ℤ) ⧸ _)⟧ := by
  by_cases hc : (g 1 0 : ZMod p) = 0
  · left
    congr 1
    apply QuotientGroup.eq.mpr
    simpa using (CongruenceSubgroup.Gamma0 p).inv_mem (CongruenceSubgroup.Gamma0_mem.mpr hc)
  · right
    let n : ℕ := ((g 0 0 : ZMod p) / (g 1 0 : ZMod p)).val
    have hcoset : ((ModularGroup.T ^ (n : ℤ) * ModularGroup.S : SL(2, ℤ)) :
        SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p) = g := by
      rw [QuotientGroup.eq, CongruenceIndex.mem_Gamma0_iff_dvd,
        CongruenceIndex.inv_mul_apply_10]
      simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
        ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
        one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add]
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [n, ZMod.natCast_zmod_val]
      field_simp
      ring
    rw [← hcoset]
    apply Quotient.sound
    change (orbitRel (Subgroup.zpowers ModularGroup.T)
      (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p)) _ _
    rw [orbitRel_apply]
    refine ⟨⟨ModularGroup.T ^ (n : ℤ), Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _⟩, ?_⟩
    change ModularGroup.T ^ (n : ℤ) •
      (ModularGroup.S : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p) = _
    rw [MulAction.Quotient.smul_coe, smul_eq_mul]

private theorem prime_cusp_representatives_ne (p : ℕ) [Fact p.Prime] :
    (⟦((1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p)⟧ :
      subgroupCusps (CongruenceSubgroup.Gamma0 p)) ≠
        ⟦(ModularGroup.S : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p)⟧ := by
  intro h
  have hs : ((1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p) ≠ ModularGroup.S := by
    intro heq
    have hmem := QuotientGroup.eq.mp heq
    have hc := CongruenceSubgroup.Gamma0_mem.mp hmem
    norm_num [ModularGroup.coe_S] at hc
  obtain ⟨u, hu⟩ := (orbitRel_apply.mp (Quotient.exact h.symm))
  have huΓ : (u : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 p := by
    apply (Subgroup.zpowers_le.mpr (show ModularGroup.T ∈ CongruenceSubgroup.Gamma0 p by
      rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.coe_T]))
    exact u.property
  have hfix : (u : SL(2, ℤ)) • ((1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p) = ((1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p) := by
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    simpa using (CongruenceSubgroup.Gamma0 p).inv_mem huΓ
  exact hs (hfix.symm.trans hu)

/-- The actual cusp orbit cardinal of `Γ₀(p)` is two at every prime level. -/
theorem gamma0GeometricCuspCount_prime (p : ℕ) [Fact p.Prime] :
    gamma0GeometricCuspCount p = 2 := by
  let f : Bool → subgroupCusps (CongruenceSubgroup.Gamma0 p) := fun b =>
    if b then ⟦(ModularGroup.S : SL(2, ℤ) ⧸ _)⟧ else ⟦((1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ _)⟧
  have hinj : Function.Injective f := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact False.elim (prime_cusp_representatives_ne p h)
    · exact False.elim (prime_cusp_representatives_ne p h.symm)
    · rfl
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      induction x using QuotientGroup.induction_on with
      | H g =>
        rcases prime_cusp_representatives p g with h | h
        · exact ⟨false, h.symm⟩
        · exact ⟨true, h.symm⟩
  change Nat.card (subgroupCusps (CongruenceSubgroup.Gamma0 p)) = 2
  rw [← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩]
  simp

end WeightTwoCusps
