module

public import WeightTwoCusps.EtaQuotient.Multiplier.HalfWeightArithmetic
public import WeightTwoCusps.EtaQuotient.Multiplier.HalfWeightSign

/-!
# Negating the arithmetic half-weight multiplier

The signed Jacobi symbol and the polynomial exponential have exactly the
same principal-root negation convention as the analytic eta multiplier.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex UpperHalfPlane
open scoped MatrixGroups

namespace WeightTwoCusps.EtaQuotient

private theorem odd_diagonal_of_mem_Gamma0_four (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) : Odd (γ 0 0) ∧ Odd (γ 1 1) := by
  have hc : (γ 1 0 : ZMod 2) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr
    exact dvd_trans (by norm_num : (2 : ℤ) ∣ 4) (Eta.level_dvd_lower_left 4 γ hγ)
  have hdet : (γ 0 0 : ZMod 2) * γ 1 1 = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod 2) γ.det_coe
    simpa only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one,
      hc, mul_zero, sub_zero] using h
  have hfinite : ∀ a d : ZMod 2, a * d = 1 → a = 1 ∧ d = 1 := by decide
  obtain ⟨ha, hd⟩ := hfinite _ _ hdet
  have hadd : (2 : ℤ) ∣ γ 0 0 - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simp only [Int.cast_sub, Int.cast_one, ha, sub_self]
  have hddd : (2 : ℤ) ∣ γ 1 1 - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simp only [Int.cast_sub, Int.cast_one, hd, sub_self]
  constructor <;> apply Int.odd_iff.mpr <;> omega

theorem odd_lowerRight_of_mem_Gamma0_four (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) : Odd (γ 1 1) :=
  (odd_diagonal_of_mem_Gamma0_four γ hγ).2

theorem upperLeft_ne_zero_of_mem_Gamma0_four (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) : γ 0 0 ≠ 0 := by
  have h := (odd_diagonal_of_mem_Gamma0_four γ hγ).1
  intro hz
  rw [hz] at h
  simp at h

theorem translationCharacter_six : translationCharacter (6 : ZMod 24) = Complex.I := by
  change ZMod.stdAddChar ((6 : ℤ) : ZMod 24) = _
  rw [ZMod.stdAddChar_coe]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  ring

theorem translationCharacter_neg_six : translationCharacter (-6 : ZMod 24) = -Complex.I := by
  rw [show (-6 : ZMod 24) = -(6 : ZMod 24) from rfl,
    AddChar.map_neg_eq_inv, translationCharacter_six, Complex.inv_I]

/-- The finite fourth-root calculation controlling simultaneous negation. -/
theorem chi_four_mul_translationCharacter {d : ℤ} (hd : Odd d) :
    (ZMod.χ₄ (-d) : ℂ) * translationCharacter ((-6 * d : ℤ) : ZMod 24) = Complex.I := by
  have hmod : d % 4 = 1 ∨ d % 4 = 3 := by
    have := Int.odd_iff.mp hd
    omega
  rcases hmod with hmod | hmod
  · have hχ : ZMod.χ₄ (-d) = -1 := by
      simpa only [Int.cast_neg] using
        ZMod.χ₄_int_three_mod_four (n := -d) (by omega)
    have he : translationCharacter ((-6 * d : ℤ) : ZMod 24) =
        translationCharacter ((-6 : ℤ) : ZMod 24) := by
      apply (translationCharacter_intCast_eq_iff _ _).mpr
      change (-6 * d) % 24 = (-6 : ℤ) % 24
      omega
    rw [hχ, he]
    norm_num [translationCharacter_neg_six]
  · have hχ : ZMod.χ₄ (-d) = 1 := by
      simpa only [Int.cast_neg] using
        ZMod.χ₄_int_one_mod_four (n := -d) (by omega)
    have he : translationCharacter ((-6 * d : ℤ) : ZMod 24) =
        translationCharacter ((6 : ℤ) : ZMod 24) := by
      apply (translationCharacter_intCast_eq_iff _ _).mpr
      change (-6 * d) % 24 = (6 : ℤ) % 24
      omega
    rw [hχ, he]
    norm_num [translationCharacter_six]

private theorem matrixMultiplierExponent_neg (γ : SL(2, ℤ)) :
    matrixMultiplierExponent (-γ) = matrixMultiplierExponent γ - 6 * γ 1 1 := by
  simpa only [matrixMultiplierExponent, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.neg_apply] using arithmeticMultiplierExponent_neg
      (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)

theorem arithmeticHalfMultiplier_neg_of_ne_zero (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) (hc : γ 1 0 ≠ 0) :
    arithmeticHalfMultiplier (-γ) = (γ 1 0).sign * Complex.I * arithmeticHalfMultiplier γ := by
  have hd := odd_lowerRight_of_mem_Gamma0_four γ hγ
  unfold arithmeticHalfMultiplier
  rw [matrixMultiplierExponent_neg]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  rw [extendedJacobi.neg_neg hc hd]
  have he : ((matrixMultiplierExponent γ - 6 * γ 1 1 : ℤ) : ZMod 24) =
      (matrixMultiplierExponent γ : ZMod 24) + ((-6 * γ 1 1 : ℤ) : ZMod 24) := by
    push_cast
    ring
  rw [he, AddChar.map_add_eq_mul]
  push_cast
  have hi := chi_four_mul_translationCharacter hd
  push_cast at hi
  linear_combination (γ 1 0).sign *
    (extendedJacobi (γ 1 0) (γ 1 1) : ℂ) *
    translationCharacter (matrixMultiplierExponent γ) * hi

theorem matrixMultiplierCharacter_neg (γ : SL(2, ℤ)) :
    translationCharacter (matrixMultiplierExponent (-γ)) =
      translationCharacter (matrixMultiplierExponent γ) *
        translationCharacter ((-6 * γ 1 1 : ℤ) : ZMod 24) := by
  rw [matrixMultiplierExponent_neg]
  have he : ((matrixMultiplierExponent γ - 6 * γ 1 1 : ℤ) : ZMod 24) =
      (matrixMultiplierExponent γ : ZMod 24) + ((-6 * γ 1 1 : ℤ) : ZMod 24) := by
    push_cast
    ring
  rw [he, AddChar.map_add_eq_mul]

/-- The arithmetic formula has the same negation rule as the analytic
half-weight multiplier, including triangular matrices. -/
theorem arithmeticHalfMultiplier_neg (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    arithmeticHalfMultiplier (-γ) =
      (if 0 < γ 1 0 ∨ γ 1 0 = 0 ∧ γ 1 1 < 0 then Complex.I else -Complex.I) *
        arithmeticHalfMultiplier γ := by
  by_cases hc : γ 1 0 = 0
  · have hdet := γ.det_coe
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with hd | hd
    · rw [ite_eq_right (by omega)]
      unfold arithmeticHalfMultiplier
      rw [matrixMultiplierCharacter_neg]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, hc, neg_zero,
        hd.2, extendedJacobi.zero_one, extendedJacobi.zero_neg_one, Int.cast_one, one_mul]
      norm_num [translationCharacter_neg_six]
      ring
    · rw [ite_eq_left (by omega)]
      unfold arithmeticHalfMultiplier
      rw [matrixMultiplierCharacter_neg]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, hc, neg_zero,
        hd.2, extendedJacobi.zero_neg_one, Int.cast_one, one_mul]
      norm_num [translationCharacter_six]
      ring
  · rw [arithmeticHalfMultiplier_neg_of_ne_zero γ hγ hc]
    rcases lt_or_gt_of_ne hc with hc | hc
    · rw [ite_eq_right (by omega), Int.sign_eq_neg_one_of_neg hc]
      norm_num
    · rw [ite_eq_left (by omega), Int.sign_eq_one_of_pos hc]
      norm_num

end WeightTwoCusps.EtaQuotient
