module

public import WeightTwoCusps.EtaQuotient.Transformation.Generation
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Generators for Γ₀(4)

A balanced Euclidean algorithm proves that `T`, the lower translation by four,
and `-I` generate `Γ₀(4)`. This is the generation step in the proof of the
arithmetic half-weight multiplier formula in §4 of Savitt's paper.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixGroups

namespace WeightTwoCusps.EtaQuotient

private theorem exists_balanced_add (x n : ℤ) (hn : n ≠ 0) :
    ∃ t : ℤ, 2 * |x + t * n| ≤ |n| := by
  have hnpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have hd : n ∣ x.bmod n.natAbs - x := by
    simpa only [Int.natCast_natAbs, abs_dvd] using
      (Int.dvd_bmod_sub_self (x := x) (m := n.natAbs))
  obtain ⟨t, ht⟩ := hd
  refine ⟨t, ?_⟩
  have he : x + t * n = x.bmod n.natAbs := by linear_combination -ht
  rw [he]
  have hnabs := Int.natCast_natAbs n
  have hlo := Int.le_bmod (x := x) hnpos
  have hhi := Int.bmod_lt (x := x) hnpos
  rcases le_total 0 (x.bmod n.natAbs) with h | h
  · rw [abs_of_nonneg h]
    omega
  · rw [abs_of_nonpos h]
    omega

private theorem upper_entries (t : ℤ) (γ : SL(2, ℤ)) :
    (ModularGroup.T ^ t * γ) 0 0 = γ 0 0 + t * γ 1 0 ∧
    (ModularGroup.T ^ t * γ) 1 0 = γ 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
    Matrix.mul_apply, Fin.sum_univ_two]

private theorem lower_entries (t : ℤ) (γ : SL(2, ℤ)) :
    (lowerTranslation t * γ) 0 0 = γ 0 0 ∧
    (lowerTranslation t * γ) 1 0 = t * γ 0 0 + γ 1 0 := by
  simp [lowerTranslation, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two]

private theorem lower_four_mem {H : Subgroup SL(2, ℤ)}
    (hL : lowerTranslation 4 ∈ H) (t : ℤ) : lowerTranslation (4 * t) ∈ H := by
  simpa only [lowerTranslation_zpow, mul_comm t] using H.zpow_mem hL t

private theorem triangular_mem {H : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ H) (hneg : (-1 : SL(2, ℤ)) ∈ H)
    (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) : γ ∈ H := by
  have hd := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hd
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hd with h | h
  · have he : γ = ModularGroup.T ^ (γ 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h.1, h.2, hc]
    rw [he]
    exact H.zpow_mem hT _
  · have he : γ = (-1 : SL(2, ℤ)) * ModularGroup.T ^ (-γ 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ModularGroup.coe_T_zpow, h.1, h.2, hc]
    rw [he]
    exact H.mul_mem hneg (H.zpow_mem hT _)

/-- The three generators in Savitt's proof generate `Γ₀(4)` without any
congruence-subgroup hypothesis on the receiving subgroup. -/
theorem Gamma0_four_le_of_generators {H : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ H) (hL : lowerTranslation 4 ∈ H)
    (hneg : (-1 : SL(2, ℤ)) ∈ H) : CongruenceSubgroup.Gamma0 4 ≤ H := by
  intro γ hγ
  generalize hm : (γ 0 0).natAbs = m
  induction m using Nat.strong_induction_on generalizing γ with
  | h m ih =>
    have hcD : (4 : ℤ) ∣ γ 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hγ
    obtain ⟨c, hc⟩ := hcD
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * (4 * c) = 1 := by
      simpa only [Matrix.det_fin_two, hc] using γ.det_coe
    have haodd : γ 0 0 % 2 = 1 := by
      have hmod : ∀ a d b c : ZMod 2, a * d - b * (4 * c) = 1 → a = 1 := by decide
      have hd := congrArg (Int.cast : ℤ → ZMod 2) hdet
      push_cast at hd
      have ha := hmod _ _ _ _ hd
      have hdiv : (2 : ℤ) ∣ γ 0 0 - 1 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
        simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using ha
      omega
    have ha0 : γ 0 0 ≠ 0 := by omega
    obtain ⟨t, ht⟩ := exists_balanced_add c (γ 0 0) ha0
    let δ := lowerTranslation (4 * t) * γ
    let c' := c + t * γ 0 0
    have hδa : δ 0 0 = γ 0 0 := (lower_entries _ γ).1
    have hδc : δ 1 0 = 4 * c' := by
      rw [(lower_entries _ γ).2, hc]
      dsimp [c']
      ring
    have hδH : δ ∈ H := by
      by_cases hc' : c' = 0
      · exact triangular_mem hT hneg δ (by rw [hδc, hc', mul_zero])
      · obtain ⟨u, hu⟩ := exists_balanced_add (δ 0 0) (4 * c') (by omega)
        let ε := ModularGroup.T ^ u * δ
        have hεa : ε 0 0 = δ 0 0 + u * (4 * c') := by
          rw [(upper_entries _ δ).1, hδc]
        have haabs : |γ 0 0| % 2 = 1 := by
          rcases abs_choice (γ 0 0) with h | h <;> rw [h] <;> omega
        have hlt : |ε 0 0| < |γ 0 0| := by
          rw [← hεa, abs_mul] at hu
          norm_num at hu
          change 2 * |c'| ≤ |γ 0 0| at ht
          omega
        have hεsmall : (ε 0 0).natAbs < m := by
          rw [← hm]
          rw [← Int.natCast_natAbs, ← Int.natCast_natAbs] at hlt
          exact_mod_cast hlt
        have hεγ : ε ∈ CongruenceSubgroup.Gamma0 4 := by
          apply CongruenceSubgroup.Gamma0_mem.mpr
          apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr
          exact ⟨c', by rw [(upper_entries _ δ).2, hδc]; norm_num⟩
        have hεH := ih (ε 0 0).natAbs hεsmall hεγ rfl
        exact (H.mul_mem_cancel_left (H.zpow_mem hT u)).mp hεH
    exact (H.mul_mem_cancel_left (lower_four_mem hL t)).mp hδH

/-- An exact statement of the three-generator presentation used here. -/
theorem Gamma0_four_eq_closure :
    CongruenceSubgroup.Gamma0 4 =
      Subgroup.closure {ModularGroup.T, lowerTranslation 4, (-1 : SL(2, ℤ))} := by
  apply le_antisymm
  · exact Gamma0_four_le_of_generators
      (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · apply (Subgroup.closure_le _).mpr
    intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl
    · norm_num [CongruenceSubgroup.Gamma0_mem, ModularGroup.T]
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr
      change (4 : ℤ) ∣ 4
      exact dvd_refl _
    · norm_num [CongruenceSubgroup.Gamma0_mem]

/-- Induction using left multiplication by the three generators and their
inverses. Equivalences allow inverse steps without a separate recurrence. -/
@[elab_as_elim] theorem Gamma0_four_induction (P : SL(2, ℤ) → Prop) (h1 : P 1)
    (hstep : ∀ g ∈ ({ModularGroup.T, lowerTranslation 4, (-1 : SL(2, ℤ))} : Set SL(2, ℤ)),
      ∀ γ ∈ CongruenceSubgroup.Gamma0 4, P (g * γ) ↔ P γ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) : P γ := by
  have hcl : γ ∈ Subgroup.closure
      {ModularGroup.T, lowerTranslation 4, (-1 : SL(2, ℤ))} := by
    rwa [← Gamma0_four_eq_closure]
  induction hcl using Subgroup.closure_induction_left with
  | one => exact h1
  | mul_left g hg δ hδ ih =>
    have hδΓ : δ ∈ CongruenceSubgroup.Gamma0 4 := by
      rwa [Gamma0_four_eq_closure]
    exact (hstep g hg δ hδΓ).mpr (ih hδΓ)
  | inv_mul_cancel g hg δ hδ ih =>
    have hgΓ : g ∈ CongruenceSubgroup.Gamma0 4 := by
      rw [Gamma0_four_eq_closure]
      exact Subgroup.subset_closure hg
    have hδΓ : δ ∈ CongruenceSubgroup.Gamma0 4 := by
      rwa [Gamma0_four_eq_closure]
    have he := hstep g hg (g⁻¹ * δ)
      ((CongruenceSubgroup.Gamma0 4).mul_mem
        ((CongruenceSubgroup.Gamma0 4).inv_mem hgΓ) hδΓ)
    simp only [mul_inv_cancel_left] at he
    exact he.mp (ih hδΓ)

end WeightTwoCusps.EtaQuotient
