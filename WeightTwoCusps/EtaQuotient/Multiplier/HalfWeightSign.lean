module

public import WeightTwoCusps.EtaQuotient.Multiplier.HalfWeight
public import WeightTwoCusps.EtaQuotient.Transformation.Generation

/-!
# Signs of the principal half-weight cocycle

The sign can be read directly from the lower-left entries when neither factor
has a zero lower-left entry. These are the square-root sign calculations used
in an arithmetic evaluation of the eta multiplier.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient

private theorem sqrt_re_pos_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) :
    0 < (Complex.sqrt w).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.2
  have h := (Complex.abs_re_lt_norm.2 hw)
  have habs := neg_abs_le w.re
  linarith

private theorem sqrt_im_pos_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    0 < (Complex.sqrt w).im := by
  rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_sqrt hw.le]
  apply Real.sqrt_pos.2
  have h := (Complex.abs_re_lt_norm.2 hw.ne')
  have habs := le_abs_self w.re
  linarith

private theorem sqrt_im_neg_of_im_neg {w : ℂ} (hw : w.im < 0) :
    (Complex.sqrt w).im < 0 := by
  rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_neg_sqrt hw]
  have h := (Complex.abs_re_lt_norm.2 hw.ne)
  have habs := le_abs_self w.re
  have : 0 < Real.sqrt ((‖w‖ - w.re) / 2) := Real.sqrt_pos.2 (by linarith)
  linarith

private theorem sqrt_im_nonneg_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) :
    0 ≤ (Complex.sqrt w).im := by
  rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_sqrt hw]
  exact Real.sqrt_nonneg _

theorem halfDenom_re_pos {γ : SL(2, ℤ)} (hc : γ 1 0 ≠ 0) (z : ℍ) :
    0 < (halfDenom γ z).re := by
  apply sqrt_re_pos_of_im_ne_zero
  change (((γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)).im) ≠ 0
  simpa using mul_ne_zero (show (γ 1 0 : ℝ) ≠ 0 by exact_mod_cast hc) z.im_pos.ne'

theorem halfDenom_im_pos {γ : SL(2, ℤ)} (hc : 0 < γ 1 0) (z : ℍ) :
    0 < (halfDenom γ z).im := by
  apply sqrt_im_pos_of_im_pos
  change 0 < (((γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)).im)
  simpa using mul_pos (show (0 : ℝ) < γ 1 0 by exact_mod_cast hc) z.im_pos

theorem halfDenom_im_neg {γ : SL(2, ℤ)} (hc : γ 1 0 < 0) (z : ℍ) :
    (halfDenom γ z).im < 0 := by
  apply sqrt_im_neg_of_im_neg
  change (((γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)).im) < 0
  simpa using mul_neg_of_neg_of_pos (show (γ 1 0 : ℝ) < 0 by exact_mod_cast hc) z.im_pos

theorem halfDenom_im_nonneg {γ : SL(2, ℤ)} (hc : 0 ≤ γ 1 0) (z : ℍ) :
    0 ≤ (halfDenom γ z).im := by
  apply sqrt_im_nonneg_of_im_nonneg
  change 0 ≤ (((γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)).im)
  simpa using mul_nonneg (show (0 : ℝ) ≤ γ 1 0 by exact_mod_cast hc) z.im_pos.le

/-- Two positive lower-left entries produce a negative sign exactly when
the product has a negative lower-left entry. -/
theorem halfCocycle_of_pos_pos {γ δ : SL(2, ℤ)}
    (hγ : 0 < γ 1 0) (hδ : 0 < δ 1 0) :
    halfCocycle γ δ = if (γ * δ) 1 0 < 0 then -1 else 1 := by
  have hp : 0 < (halfDenom γ (δ • UpperHalfPlane.I) *
      halfDenom δ UpperHalfPlane.I).im := by
    rw [Complex.mul_im]
    exact add_pos
      (mul_pos (halfDenom_re_pos hγ.ne' _) (halfDenom_im_pos hδ _))
      (mul_pos (halfDenom_im_pos hγ _) (halfDenom_re_pos hδ.ne' _))
  have h := congrArg Complex.im (halfDenom_mul γ δ UpperHalfPlane.I)
  rcases halfCocycle_eq_one_or_neg_one γ δ with heq | heq
  · rw [heq, one_mul] at h
    by_cases hc : (γ * δ) 1 0 < 0
    · have := halfDenom_im_neg hc UpperHalfPlane.I
      linarith
    · rw [ite_eq_right hc]
      exact heq
  · rw [heq, neg_one_mul, Complex.neg_im] at h
    by_cases hc : (γ * δ) 1 0 < 0
    · rw [ite_eq_left hc]
      exact heq
    · have := halfDenom_im_nonneg (le_of_not_gt hc) UpperHalfPlane.I
      linarith

/-- Two negative lower-left entries produce a positive sign exactly when
the product still has a negative lower-left entry. The zero boundary is negative. -/
theorem halfCocycle_of_neg_neg {γ δ : SL(2, ℤ)}
    (hγ : γ 1 0 < 0) (hδ : δ 1 0 < 0) :
    halfCocycle γ δ = if (γ * δ) 1 0 < 0 then 1 else -1 := by
  have hp : (halfDenom γ (δ • UpperHalfPlane.I) *
      halfDenom δ UpperHalfPlane.I).im < 0 := by
    rw [Complex.mul_im]
    exact add_neg
      (mul_neg_of_pos_of_neg (halfDenom_re_pos hγ.ne _) (halfDenom_im_neg hδ _))
      (mul_neg_of_neg_of_pos (halfDenom_im_neg hγ _) (halfDenom_re_pos hδ.ne _))
  have h := congrArg Complex.im (halfDenom_mul γ δ UpperHalfPlane.I)
  rcases halfCocycle_eq_one_or_neg_one γ δ with heq | heq
  · rw [heq, one_mul] at h
    by_cases hc : (γ * δ) 1 0 < 0
    · rw [ite_eq_left hc]
      exact heq
    · have := halfDenom_im_nonneg (le_of_not_gt hc) UpperHalfPlane.I
      linarith
  · rw [heq, neg_one_mul, Complex.neg_im] at h
    by_cases hc : (γ * δ) 1 0 < 0
    · have := halfDenom_im_neg hc UpperHalfPlane.I
      linarith
    · rw [ite_eq_right hc]
      exact heq

private theorem halfDenom_re_nonneg (γ : SL(2, ℤ)) (z : ℍ) :
    0 ≤ (halfDenom γ z).re := by
  rw [halfDenom, Complex.sqrt, Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

private theorem halfCocycle_eq_one_of_re_pos {γ δ : SL(2, ℤ)}
    (hp : 0 < (halfDenom γ (δ • UpperHalfPlane.I) *
      halfDenom δ UpperHalfPlane.I).re) : halfCocycle γ δ = 1 := by
  rcases halfCocycle_eq_one_or_neg_one γ δ with heq | heq
  · exact heq
  · have h := congrArg Complex.re (halfDenom_mul γ δ UpperHalfPlane.I)
    rw [heq, neg_one_mul, Complex.neg_re] at h
    have := halfDenom_re_nonneg (γ * δ) UpperHalfPlane.I
    linarith

private theorem halfCocycle_eq_neg_one_of_re_neg {γ δ : SL(2, ℤ)}
    (hp : (halfDenom γ (δ • UpperHalfPlane.I) *
      halfDenom δ UpperHalfPlane.I).re < 0) : halfCocycle γ δ = -1 := by
  rcases halfCocycle_eq_one_or_neg_one γ δ with heq | heq
  · have h := congrArg Complex.re (halfDenom_mul γ δ UpperHalfPlane.I)
    rw [heq, one_mul] at h
    have := halfDenom_re_nonneg (γ * δ) UpperHalfPlane.I
    linarith
  · exact heq

/-- Opposite signs of the lower-left entries never cross the principal
square-root branch cut. -/
theorem halfCocycle_of_pos_neg {γ δ : SL(2, ℤ)}
    (hγ : 0 < γ 1 0) (hδ : δ 1 0 < 0) : halfCocycle γ δ = 1 := by
  have hp : 0 < (halfDenom γ (δ • UpperHalfPlane.I) *
      halfDenom δ UpperHalfPlane.I).re := by
    rw [Complex.mul_re]
    have h₁ := mul_pos (halfDenom_re_pos hγ.ne' (δ • UpperHalfPlane.I))
      (halfDenom_re_pos hδ.ne UpperHalfPlane.I)
    have h₂ := mul_neg_of_pos_of_neg (halfDenom_im_pos hγ (δ • UpperHalfPlane.I))
      (halfDenom_im_neg hδ UpperHalfPlane.I)
    linarith
  rcases halfCocycle_eq_one_or_neg_one γ δ with heq | heq
  · exact heq
  · have h := congrArg Complex.re (halfDenom_mul γ δ UpperHalfPlane.I)
    rw [heq, neg_one_mul, Complex.neg_re] at h
    have := halfDenom_re_nonneg (γ * δ) UpperHalfPlane.I
    linarith

theorem halfCocycle_of_neg_pos {γ δ : SL(2, ℤ)}
    (hγ : γ 1 0 < 0) (hδ : 0 < δ 1 0) : halfCocycle γ δ = 1 := by
  have hp : 0 < (halfDenom γ (δ • UpperHalfPlane.I) *
      halfDenom δ UpperHalfPlane.I).re := by
    rw [Complex.mul_re]
    have h₁ := mul_pos (halfDenom_re_pos hγ.ne (δ • UpperHalfPlane.I))
      (halfDenom_re_pos hδ.ne' UpperHalfPlane.I)
    have h₂ := mul_neg_of_neg_of_pos (halfDenom_im_neg hγ (δ • UpperHalfPlane.I))
      (halfDenom_im_pos hδ UpperHalfPlane.I)
    linarith
  rcases halfCocycle_eq_one_or_neg_one γ δ with heq | heq
  · exact heq
  · have h := congrArg Complex.re (halfDenom_mul γ δ UpperHalfPlane.I)
    rw [heq, neg_one_mul, Complex.neg_re] at h
    have := halfDenom_re_nonneg (γ * δ) UpperHalfPlane.I
    linarith

/-- Entrywise evaluation of the cocycle away from zero lower-left entries.
The asymmetry at a zero product entry records the principal square root's
choice on the negative real axis. -/
theorem halfCocycle_of_ne_zero {γ δ : SL(2, ℤ)}
    (hγ : γ 1 0 ≠ 0) (hδ : δ 1 0 ≠ 0) :
    halfCocycle γ δ =
      if 0 < γ 1 0 ∧ 0 < δ 1 0 ∧ (γ * δ) 1 0 < 0 ∨
        γ 1 0 < 0 ∧ δ 1 0 < 0 ∧ 0 ≤ (γ * δ) 1 0 then -1 else 1 := by
  rcases lt_or_gt_of_ne hγ with hγ | hγ <;> rcases lt_or_gt_of_ne hδ with hδ | hδ
  · rw [halfCocycle_of_neg_neg hγ hδ]
    by_cases h : (γ * δ) 1 0 < 0
    · rw [ite_eq_left h, ite_eq_right]
      omega
    · rw [ite_eq_right h, ite_eq_left]
      omega
  · rw [halfCocycle_of_neg_pos hγ hδ, ite_eq_right]
    omega
  · rw [halfCocycle_of_pos_neg hγ hδ, ite_eq_right]
    omega
  · rw [halfCocycle_of_pos_pos hγ hδ]
    by_cases h : (γ * δ) 1 0 < 0
    · rw [ite_eq_left h, ite_eq_left]
      omega
    · rw [ite_eq_right h, ite_eq_right]
      omega

theorem halfDenom_of_zero_one {γ : SL(2, ℤ)}
    (hc : γ 1 0 = 0) (hd : γ 1 1 = 1) (z : ℍ) : halfDenom γ z = 1 := by
  simp [halfDenom, UpperHalfPlane.denom, hc, hd]

theorem halfDenom_of_zero_neg_one {γ : SL(2, ℤ)}
    (hc : γ 1 0 = 0) (hd : γ 1 1 = -1) (z : ℍ) : halfDenom γ z = Complex.I := by
  simpa [halfDenom, UpperHalfPlane.denom, hc, hd] using Complex.sqrt_neg_one

theorem halfCocycle_of_left_zero_one {γ δ : SL(2, ℤ)}
    (hc : γ 1 0 = 0) (hd : γ 1 1 = 1) : halfCocycle γ δ = 1 := by
  have heq (z : ℍ) : halfDenom (γ * δ) z = halfDenom δ z := by
    simp [halfDenom, UpperHalfPlane.denom,
      Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
  have h := halfDenom_mul γ δ UpperHalfPlane.I
  rw [halfDenom_of_zero_one hc hd, one_mul, heq] at h
  exact (mul_eq_right₀ (halfDenom_ne_zero δ UpperHalfPlane.I)).mp h

theorem halfCocycle_of_left_zero_neg_one {γ δ : SL(2, ℤ)}
    (hc : γ 1 0 = 0) (hd : γ 1 1 = -1) (hδ : δ 1 0 ≠ 0) :
    halfCocycle γ δ = if 0 < δ 1 0 then -1 else 1 := by
  by_cases hδpos : 0 < δ 1 0
  · rw [ite_eq_left hδpos]
    apply halfCocycle_eq_neg_one_of_re_neg
    rw [halfDenom_of_zero_neg_one hc hd, Complex.mul_re]
    simpa using neg_neg_of_pos (halfDenom_im_pos hδpos UpperHalfPlane.I)
  · rw [ite_eq_right hδpos]
    apply halfCocycle_eq_one_of_re_pos
    rw [halfDenom_of_zero_neg_one hc hd, Complex.mul_re]
    have hδneg : δ 1 0 < 0 := by omega
    simpa using neg_pos.mpr (halfDenom_im_neg hδneg UpperHalfPlane.I)

theorem halfCocycle_of_right_zero_one {γ δ : SL(2, ℤ)}
    (hγ : γ 1 0 ≠ 0) (hc : δ 1 0 = 0) (hd : δ 1 1 = 1) :
    halfCocycle γ δ = 1 := by
  apply halfCocycle_eq_one_of_re_pos
  rw [halfDenom_of_zero_one hc hd, mul_one]
  exact halfDenom_re_pos hγ _

theorem halfCocycle_of_right_zero_neg_one {γ δ : SL(2, ℤ)}
    (hγ : γ 1 0 ≠ 0) (hc : δ 1 0 = 0) (hd : δ 1 1 = -1) :
    halfCocycle γ δ = if 0 < γ 1 0 then -1 else 1 := by
  by_cases hγpos : 0 < γ 1 0
  · rw [ite_eq_left hγpos]
    apply halfCocycle_eq_neg_one_of_re_neg
    rw [halfDenom_of_zero_neg_one hc hd, Complex.mul_re]
    simpa using neg_neg_of_pos (halfDenom_im_pos hγpos (δ • UpperHalfPlane.I))
  · rw [ite_eq_right hγpos]
    apply halfCocycle_eq_one_of_re_pos
    rw [halfDenom_of_zero_neg_one hc hd, Complex.mul_re]
    have hγneg : γ 1 0 < 0 := by omega
    simpa using neg_pos.mpr (halfDenom_im_neg hγneg (δ • UpperHalfPlane.I))

@[simp] theorem halfCocycle_T_zpow_left (n : ℤ) (γ : SL(2, ℤ)) :
    halfCocycle (ModularGroup.T ^ n) γ = 1 := by
  apply halfCocycle_of_left_zero_one <;> simp [ModularGroup.coe_T_zpow]

/-- The lower translation sign needed in the positive-entry reduction for
the arithmetic multiplier formula. -/
theorem halfCocycle_lowerTranslation_pos {n : ℤ} {γ : SL(2, ℤ)}
    (hn : 0 < n) (ha : 0 ≤ γ 0 0) (hc : 0 < γ 1 0) :
    halfCocycle (lowerTranslation n) γ = 1 := by
  rw [halfCocycle_of_pos_pos (by simpa [lowerTranslation] using hn) hc]
  rw [ite_eq_right]
  have he : (lowerTranslation n * γ) 1 0 = n * γ 0 0 + γ 1 0 := by
    simp [lowerTranslation, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  rw [he]
  have := mul_nonneg hn.le ha
  omega

theorem halfCocycle_lowerTranslation_neg {n : ℤ} {γ : SL(2, ℤ)}
    (hn : n < 0) (hc : 0 < γ 1 0) : halfCocycle (lowerTranslation n) γ = 1 := by
  apply halfCocycle_of_neg_pos _ hc
  simpa [lowerTranslation] using hn

private def translationHalfMultiplier : Multiplicative ℤ →* ℂ where
  toFun n := halfMultiplier (ModularGroup.T ^ n.toAdd)
  map_one' := by simp
  map_mul' x y := by
    change halfMultiplier (ModularGroup.T ^ (x.toAdd + y.toAdd)) = _
    rw [zpow_add, halfMultiplier_mul, halfCocycle_T_zpow_left, mul_one]

theorem halfMultiplier_T_zpow (n : ℤ) :
    halfMultiplier (ModularGroup.T ^ n) = translationCharacter n := by
  have h := translationHalfMultiplier.map_zpow (Multiplicative.ofAdd 1) n
  have he : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
    apply Multiplicative.toAdd.injective
    simp
  rw [he] at h
  change halfMultiplier (ModularGroup.T ^ n) = halfMultiplier (ModularGroup.T ^ (1 : ℤ)) ^ n at h
  rw [zpow_one, halfMultiplier_T] at h
  rw [h, ← AddChar.map_zsmul_eq_zpow]
  simp

@[simp] theorem halfMultiplier_neg_one : halfMultiplier (-1 : SL(2, ℤ)) = -Complex.I := by
  have hneg : (-1 : SL(2, ℤ)) • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [show (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) from rfl,
      ModularGroup.SL_neg_smul, one_smul]
  have hc : (-1 : SL(2, ℤ)) 1 0 = 0 := by norm_num
  have hd : (-1 : SL(2, ℤ)) 1 1 = -1 := by norm_num
  rw [halfMultiplier, hneg, halfDenom_of_zero_neg_one hc hd,
    mul_comm Complex.I, div_mul_eq_div_div,
    div_self (ModularForm.eta_ne_zero UpperHalfPlane.I.im_pos), one_div, Complex.inv_I]

theorem halfMultiplier_S_inv :
    halfMultiplier (ModularGroup.S⁻¹) = (halfMultiplier ModularGroup.S)⁻¹ := by
  have h := halfMultiplier_mul ModularGroup.S ModularGroup.S⁻¹
  have hc : halfCocycle ModularGroup.S ModularGroup.S⁻¹ = 1 := by
    apply halfCocycle_of_pos_neg <;> norm_num [ModularGroup.S_inv, ModularGroup.S]
  rw [mul_inv_cancel, halfMultiplier_one, hc, mul_one] at h
  apply mul_left_cancel₀ (halfMultiplier_ne_zero ModularGroup.S)
  rw [mul_inv_cancel₀ (halfMultiplier_ne_zero ModularGroup.S)]
  exact h.symm

/-- Every integral lower translation has the opposite translation character. -/
theorem halfMultiplier_lowerTranslation (n : ℤ) :
    halfMultiplier (lowerTranslation n) = translationCharacter (-n) := by
  have he : lowerTranslation n =
      (ModularGroup.S * ModularGroup.T ^ (-n)) * ModularGroup.S⁻¹ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerTranslation, ModularGroup.S,
        ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hc₁ : (ModularGroup.S * ModularGroup.T ^ (-n)) 1 0 = 1 := by
    simp [ModularGroup.S, ModularGroup.coe_T_zpow,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hc₂ : halfCocycle (ModularGroup.S * ModularGroup.T ^ (-n)) ModularGroup.S⁻¹ = 1 := by
    apply halfCocycle_of_pos_neg
    · rw [hc₁]; norm_num
    · norm_num [ModularGroup.S_inv, ModularGroup.S]
  have hc₃ : halfCocycle ModularGroup.S (ModularGroup.T ^ (-n)) = 1 := by
    apply halfCocycle_of_right_zero_one
    · norm_num [ModularGroup.S]
    · simp [ModularGroup.coe_T_zpow]
    · simp [ModularGroup.coe_T_zpow]
  rw [he, halfMultiplier_mul, hc₂, mul_one, halfMultiplier_mul, hc₃, mul_one,
    halfMultiplier_T_zpow, halfMultiplier_S_inv]
  field_simp [halfMultiplier_ne_zero ModularGroup.S]
  simp

private theorem lower_right_of_lower_left_zero {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) :
    γ 1 1 = 1 ∨ γ 1 1 = -1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
  exact Int.eq_one_or_neg_one_of_mul_eq_one (by simpa [mul_comm] using h)

theorem halfCocycle_of_zero_zero {γ δ : SL(2, ℤ)}
    (hγ : γ 1 0 = 0) (hδ : δ 1 0 = 0) :
    halfCocycle γ δ = if γ 1 1 = -1 ∧ δ 1 1 = -1 then -1 else 1 := by
  have hc : (γ * δ) 1 0 = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hγ, hδ]
  have hd : (γ * δ) 1 1 = γ 1 1 * δ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hγ]
  rcases lower_right_of_lower_left_zero hγ with hγd | hγd
  · rw [halfCocycle_of_left_zero_one hγ hγd, ite_eq_right]
    omega
  · rcases lower_right_of_lower_left_zero hδ with hδd | hδd
    · rw [ite_eq_right (by omega : ¬(γ 1 1 = -1 ∧ δ 1 1 = -1))]
      have hd' : (γ * δ) 1 1 = -1 := by rw [hd, hγd, hδd]; norm_num
      have h := halfDenom_mul γ δ UpperHalfPlane.I
      rw [halfDenom_of_zero_neg_one hc hd', halfDenom_of_zero_neg_one hγ hγd,
        halfDenom_of_zero_one hδ hδd, mul_one] at h
      exact (mul_eq_right₀ Complex.I_ne_zero).mp h
    · rw [ite_eq_left ⟨hγd, hδd⟩]
      have hd' : (γ * δ) 1 1 = 1 := by rw [hd, hγd, hδd]; norm_num
      have h := halfDenom_mul γ δ UpperHalfPlane.I
      rw [halfDenom_of_zero_one hc hd', halfDenom_of_zero_neg_one hγ hγd,
        halfDenom_of_zero_neg_one hδ hδd, mul_one, Complex.I_mul_I] at h
      exact h

@[simp] theorem halfCocycle_T_zpow_right (γ : SL(2, ℤ)) (n : ℤ) :
    halfCocycle γ (ModularGroup.T ^ n) = 1 := by
  by_cases hγ : γ 1 0 = 0
  · rw [halfCocycle_of_zero_zero hγ (by simp [ModularGroup.coe_T_zpow]), ite_eq_right]
    simp [ModularGroup.coe_T_zpow]
  · exact halfCocycle_of_right_zero_one hγ
      (by simp [ModularGroup.coe_T_zpow]) (by simp [ModularGroup.coe_T_zpow])

theorem halfMultiplier_T_zpow_mul (n : ℤ) (γ : SL(2, ℤ)) :
    halfMultiplier (ModularGroup.T ^ n * γ) = translationCharacter n * halfMultiplier γ := by
  rw [halfMultiplier_mul, halfCocycle_T_zpow_left, mul_one, halfMultiplier_T_zpow]

theorem halfMultiplier_mul_T_zpow (γ : SL(2, ℤ)) (n : ℤ) :
    halfMultiplier (γ * ModularGroup.T ^ n) = halfMultiplier γ * translationCharacter n := by
  rw [halfMultiplier_mul, halfCocycle_T_zpow_right, mul_one, halfMultiplier_T_zpow]

theorem halfMultiplier_neg_of_pos {γ : SL(2, ℤ)} (hc : 0 < γ 1 0) :
    halfMultiplier (-γ) = Complex.I * halfMultiplier γ := by
  have he : (-1 : SL(2, ℤ)) * γ = -γ := by simp
  have hs : halfCocycle (-1 : SL(2, ℤ)) γ = -1 := by
    rw [halfCocycle_of_left_zero_neg_one (by norm_num) (by norm_num) hc.ne',
      ite_eq_left hc]
  rw [← he, halfMultiplier_mul, halfMultiplier_neg_one, hs]
  ring

theorem halfMultiplier_neg_of_neg {γ : SL(2, ℤ)} (hc : γ 1 0 < 0) :
    halfMultiplier (-γ) = -Complex.I * halfMultiplier γ := by
  have he : (-1 : SL(2, ℤ)) * γ = -γ := by simp
  have hs : halfCocycle (-1 : SL(2, ℤ)) γ = 1 := by
    rw [halfCocycle_of_left_zero_neg_one (by norm_num) (by norm_num) hc.ne,
      ite_eq_right (by omega : ¬0 < γ 1 0)]
  rw [← he, halfMultiplier_mul, halfMultiplier_neg_one, hs, mul_one]

/-- A complete entrywise formula, including the triangular boundary cases. -/
theorem halfCocycle_eq_entry_sign (γ δ : SL(2, ℤ)) :
    halfCocycle γ δ =
      if γ 1 0 = 0 then
        if γ 1 1 = 1 then 1
        else if 0 < δ 1 0 ∨ δ 1 0 = 0 ∧ δ 1 1 = -1 then -1 else 1
      else if δ 1 0 = 0 then
        if δ 1 1 = 1 then 1 else if 0 < γ 1 0 then -1 else 1
      else if 0 < γ 1 0 ∧ 0 < δ 1 0 ∧ (γ * δ) 1 0 < 0 ∨
        γ 1 0 < 0 ∧ δ 1 0 < 0 ∧ 0 ≤ (γ * δ) 1 0 then -1 else 1 := by
  by_cases hγ : γ 1 0 = 0
  · rw [ite_eq_left hγ]
    rcases lower_right_of_lower_left_zero hγ with hdγ | hdγ
    · rw [ite_eq_left hdγ, halfCocycle_of_left_zero_one hγ hdγ]
    · rw [ite_eq_right (by omega : ¬γ 1 1 = 1)]
      by_cases hδ : δ 1 0 = 0
      · rw [halfCocycle_of_zero_zero hγ hδ]
        simp only [hdγ, hδ]
        norm_num
      · rw [halfCocycle_of_left_zero_neg_one hγ hdγ hδ]
        simp only [hδ, false_and, or_false]
  · rw [ite_eq_right hγ]
    by_cases hδ : δ 1 0 = 0
    · rw [ite_eq_left hδ]
      rcases lower_right_of_lower_left_zero hδ with hdδ | hdδ
      · rw [ite_eq_left hdδ, halfCocycle_of_right_zero_one hγ hδ hdδ]
      · rw [ite_eq_right (by omega : ¬δ 1 1 = 1),
          halfCocycle_of_right_zero_neg_one hγ hδ hdδ]
    · rw [ite_eq_right hδ, halfCocycle_of_ne_zero hγ hδ]

theorem halfCocycle_neg_one_left (γ : SL(2, ℤ)) :
    halfCocycle (-1 : SL(2, ℤ)) γ =
      if 0 < γ 1 0 ∨ γ 1 0 = 0 ∧ γ 1 1 < 0 then -1 else 1 := by
  rw [halfCocycle_eq_entry_sign]
  norm_num
  by_cases hc : γ 1 0 = 0
  · rcases lower_right_of_lower_left_zero hc with hd | hd <;>
      simp only [hc, hd] <;> norm_num
  · simp only [hc, false_and, or_false]

/-- Negation with the principal-root boundary convention made explicit. -/
theorem halfMultiplier_neg (γ : SL(2, ℤ)) :
    halfMultiplier (-γ) =
      (if 0 < γ 1 0 ∨ γ 1 0 = 0 ∧ γ 1 1 < 0 then Complex.I else -Complex.I) *
        halfMultiplier γ := by
  have he : (-1 : SL(2, ℤ)) * γ = -γ := by simp
  rw [← he, halfMultiplier_mul, halfMultiplier_neg_one, halfCocycle_neg_one_left]
  split_ifs <;> ring

end WeightTwoCusps.EtaQuotient
