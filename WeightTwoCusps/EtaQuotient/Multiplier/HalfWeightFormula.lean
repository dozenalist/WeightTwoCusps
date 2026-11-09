module

public import WeightTwoCusps.EtaQuotient.Multiplier.HalfWeightArithmetic
public import WeightTwoCusps.EtaQuotient.Multiplier.HalfWeightSign
public import WeightTwoCusps.EtaQuotient.Multiplier.ArithmeticNegation

/-!
# Generator recurrences for the arithmetic eta multiplier

The lower-translation recurrence combines signed Jacobi periodicity with
the polynomial exponent congruence. Its analytic counterpart uses the
principal-root sign calculation.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex UpperHalfPlane
open scoped MatrixGroups

namespace WeightTwoCusps.EtaQuotient

private theorem matrix_det (γ : SL(2, ℤ)) :
    γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using γ.det_coe

private theorem lower_four_entries (γ : SL(2, ℤ)) :
    (lowerTranslation 4 * γ) 1 0 = γ 1 0 + 4 * γ 0 0 ∧
    (lowerTranslation 4 * γ) 1 1 = γ 1 1 + 4 * γ 0 1 := by
  simp [lowerTranslation, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, add_comm]

/-- The arithmetic lower-translation recurrence when the upper-left entry
is positive. This is the Jacobi and exponential calculation of Savitt 4.12. -/
theorem arithmeticHalfMultiplier_lower_four_mul (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) (ha : 0 < γ 0 0)
    (hd : Odd (γ 1 1)) :
    arithmeticHalfMultiplier (lowerTranslation 4 * γ) =
      arithmeticHalfMultiplier γ * translationCharacter (-4) := by
  unfold arithmeticHalfMultiplier
  rw [matrixMultiplierCharacter_lowerTranslation_four γ hγ,
    (lower_four_entries γ).1, (lower_four_entries γ).2,
    extendedJacobi_lower_four ha hd (matrix_det γ), mul_assoc]

/-- There is no square-root sign at the lower generator when `a > 0`. -/
theorem halfCocycle_lower_four_of_upperLeft_pos (γ : SL(2, ℤ))
    (ha : 0 < γ 0 0) : halfCocycle (lowerTranslation 4) γ = 1 := by
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · apply halfCocycle_of_pos_neg _ hc
    norm_num [lowerTranslation]
  · have hdet : γ 0 0 * γ 1 1 = 1 := by simpa [hc] using matrix_det γ
    have hd : γ 1 1 = 1 := by
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with h | h <;> omega
    apply halfCocycle_of_right_zero_one _ hc hd
    norm_num [lowerTranslation]
  · exact halfCocycle_lowerTranslation_pos (by norm_num) ha.le hc

theorem halfMultiplier_lower_four_mul (γ : SL(2, ℤ)) (ha : 0 < γ 0 0) :
    halfMultiplier (lowerTranslation 4 * γ) =
      halfMultiplier γ * translationCharacter (-4) := by
  rw [halfMultiplier_mul, halfMultiplier_lowerTranslation,
    halfCocycle_lower_four_of_upperLeft_pos γ ha, mul_one, mul_comm]
  norm_num

private theorem gamma0_four_neg_mem {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    -γ ∈ CongruenceSubgroup.Gamma0 4 := by
  simpa [CongruenceSubgroup.Gamma0_mem] using hγ

private theorem multiplier_formula_neg_iff (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    arithmeticHalfMultiplier (-γ) = halfMultiplier (-γ) ↔
      arithmeticHalfMultiplier γ = halfMultiplier γ := by
  rw [arithmeticHalfMultiplier_neg γ hγ, halfMultiplier_neg]
  have hc : (if 0 < γ 1 0 ∨ γ 1 0 = 0 ∧ γ 1 1 < 0 then Complex.I else -Complex.I) ≠ 0 := by
    split_ifs <;> simp
  exact ⟨mul_left_cancel₀ hc, fun h ↦ by rw [h]⟩

private theorem multiplier_formula_T_iff (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    arithmeticHalfMultiplier (ModularGroup.T * γ) = halfMultiplier (ModularGroup.T * γ) ↔
      arithmeticHalfMultiplier γ = halfMultiplier γ := by
  rw [arithmeticHalfMultiplier_T_mul γ hγ]
  have he : halfMultiplier (ModularGroup.T * γ) = halfMultiplier γ * translationCharacter 1 := by
    simpa [mul_comm] using halfMultiplier_T_zpow_mul 1 γ
  rw [he]
  have hc : translationCharacter 1 ≠ 0 := (ZMod.toCircle _).coe_ne_zero
  exact ⟨mul_right_cancel₀ hc, fun h ↦ by rw [h]⟩

private theorem multiplier_formula_lower_four_iff_pos (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) (ha : 0 < γ 0 0) :
    arithmeticHalfMultiplier (lowerTranslation 4 * γ) = halfMultiplier (lowerTranslation 4 * γ) ↔
      arithmeticHalfMultiplier γ = halfMultiplier γ := by
  rw [arithmeticHalfMultiplier_lower_four_mul γ hγ ha
    (odd_lowerRight_of_mem_Gamma0_four γ hγ), halfMultiplier_lower_four_mul γ ha]
  have hc : translationCharacter (-4) ≠ 0 := (ZMod.toCircle _).coe_ne_zero
  exact ⟨mul_right_cancel₀ hc, fun h ↦ by rw [h]⟩

private theorem multiplier_formula_lower_four_iff (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    arithmeticHalfMultiplier (lowerTranslation 4 * γ) = halfMultiplier (lowerTranslation 4 * γ) ↔
      arithmeticHalfMultiplier γ = halfMultiplier γ := by
  by_cases ha : 0 < γ 0 0
  · exact multiplier_formula_lower_four_iff_pos γ hγ ha
  · have ha0 := upperLeft_ne_zero_of_mem_Gamma0_four γ hγ
    have ha' : 0 < (-γ) 0 0 := by simpa using (show 0 < -γ 0 0 by omega)
    have hL : lowerTranslation 4 * γ ∈ CongruenceSubgroup.Gamma0 4 := by
      apply (CongruenceSubgroup.Gamma0 4).mul_mem _ hγ
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr
      change (4 : ℤ) ∣ 4
      exact dvd_refl _
    have h := multiplier_formula_lower_four_iff_pos (-γ) (gamma0_four_neg_mem hγ) ha'
    rw [mul_neg, multiplier_formula_neg_iff _ hL, multiplier_formula_neg_iff _ hγ] at h
    exact h

/-- Savitt's arithmetic eta-multiplier formula on `Γ₀(4)`, with the
principal-square-root and signed-Jacobi conventions, including `c = 0`. -/
theorem halfMultiplier_eq_arithmetic (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    halfMultiplier γ = arithmeticHalfMultiplier γ := by
  symm
  apply Gamma0_four_induction (fun δ ↦ arithmeticHalfMultiplier δ = halfMultiplier δ)
    (by simp) ?_ γ hγ
  intro g hg δ hδ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact multiplier_formula_T_iff δ hδ
  · exact multiplier_formula_lower_four_iff δ hδ
  · simpa only [neg_one_mul] using multiplier_formula_neg_iff δ hδ

/-- The customary Jacobi-symbol form of the unsquared eta multiplier. -/
theorem halfMultiplier_eq_extendedJacobi (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    halfMultiplier γ = (extendedJacobi (γ 1 0) (γ 1 1) : ℂ) *
      translationCharacter (matrixMultiplierExponent γ) :=
  halfMultiplier_eq_arithmetic γ hγ

end WeightTwoCusps.EtaQuotient
