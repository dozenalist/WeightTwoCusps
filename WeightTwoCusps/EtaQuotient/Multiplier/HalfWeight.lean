module

public import WeightTwoCusps.EtaQuotient.Multiplier.Basic
public import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# The half-weight eta multiplier

The principal square root of `cz+d` determines the unsquared eta multiplier.
Continuity proves that this multiplier is constant on `ℍ`, and its square is
the already computed eta-square character. This supplies the analytic
half-weight object. Its Jacobi-symbol formula is proved in `HalfWeightFormula.lean`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient

/-- The principal square-root denominator in the half-weight slash operator. -/
def halfDenom (γ : SL(2, ℤ)) (z : ℍ) : ℂ := Complex.sqrt (denom γ z)

@[simp] theorem halfDenom_sq (γ : SL(2, ℤ)) (z : ℍ) : halfDenom γ z ^ 2 = denom γ z :=
  Complex.cpow_ofNat_inv_pow _ 2

theorem halfDenom_ne_zero (γ : SL(2, ℤ)) (z : ℍ) : halfDenom γ z ≠ 0 := by
  intro hz
  have h := halfDenom_sq γ z
  rw [hz, zero_pow (by decide : 2 ≠ 0)] at h
  exact denom_ne_zero γ z h.symm

theorem halfDenom_continuous (γ : SL(2, ℤ)) : Continuous (halfDenom γ) := by
  have hd : Continuous (fun z : ℍ ↦ denom γ z) := by
    change Continuous (fun z : ℍ ↦ (γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ))
    fun_prop
  by_cases hc : γ 1 0 = 0
  · have heq : halfDenom γ = fun _ : ℍ ↦ Complex.sqrt (γ 1 1 : ℂ) := by
      ext z
      simp [halfDenom, UpperHalfPlane.denom, hc]
    rw [heq]
    exact continuous_const
  · apply continuous_iff_continuousAt.mpr
    intro z
    change ContinuousAt (fun w : ℍ ↦ Complex.sqrt (denom γ w)) z
    have him : (denom γ z).im ≠ 0 := by
      change (((γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)).im) ≠ 0
      simpa using mul_ne_zero (show (γ 1 0 : ℝ) ≠ 0 by exact_mod_cast hc) z.im_pos.ne'
    exact ContinuousAt.comp (f := fun w : ℍ ↦ denom γ w)
      (Complex.continuousAt_sqrt (Or.inr him)) hd.continuousAt

/-- The actual half-weight multiplier, with the principal-square-root convention. -/
def halfMultiplier (γ : SL(2, ℤ)) : ℂ :=
  ModularForm.eta (γ • UpperHalfPlane.I : ℍ) /
    (halfDenom γ UpperHalfPlane.I * ModularForm.eta UpperHalfPlane.I)

private theorem halfRatio_sq (γ : SL(2, ℤ)) (z : ℍ) :
    (ModularForm.eta (γ • z : ℍ) / (halfDenom γ z * ModularForm.eta z)) ^ 2 =
      Eta.etaMultiplier (Eta.etaExponent γ) := by
  rw [div_pow, mul_pow, halfDenom_sq]
  change Eta.etaSq (γ • z) / (denom γ z * Eta.etaSq z) = _
  rw [Eta.etaSq_modular_transform]
  field_simp [Eta.etaSq, denom_ne_zero γ z, ModularForm.eta_ne_zero z.im_pos]

/-- The half-weight slash ratio is independent of the point. -/
theorem halfRatio_eq_multiplier (γ : SL(2, ℤ)) (z : ℍ) :
    ModularForm.eta (γ • z : ℍ) / (halfDenom γ z * ModularForm.eta z) = halfMultiplier γ := by
  let f : ℍ → ℂ := fun w ↦ ModularForm.eta (γ • w : ℍ) /
    (halfDenom γ w * ModularForm.eta w)
  have hη : Continuous (fun w : ℍ ↦ ModularForm.eta w) := by
    convert! (holo 1 (fun _ ↦ (1 : ℤ))).continuous using 1
    ext w
    simp [etaQuotient, exponent]
  have hγ : Continuous (fun w : ℍ ↦ γ • w) := by
    change Continuous (fun w : ℍ ↦ (Matrix.SpecialLinearGroup.mapGL ℝ γ) • w)
    exact continuous_const_smul _
  have hf : Continuous f := (hη.comp hγ).div ((halfDenom_continuous γ).mul hη)
    (fun w ↦ mul_ne_zero (halfDenom_ne_zero γ w) (ModularForm.eta_ne_zero w.im_pos))
  have hs (w : ℍ) : f w ^ 2 = f UpperHalfPlane.I ^ 2 :=
    (halfRatio_sq γ w).trans (halfRatio_sq γ UpperHalfPlane.I).symm
  have hm : Set.MapsTo f Set.univ {f UpperHalfPlane.I, -f UpperHalfPlane.I} := by
    intro w _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (sq_eq_sq_iff_eq_or_eq_neg.mp (hs w))
  exact isPreconnected_univ.constant_of_mapsTo (Set.toFinite _).isDiscrete hf.continuousOn hm
    (Set.mem_univ z) (Set.mem_univ UpperHalfPlane.I)

/-- The unsquared eta transformation law at every integral modular matrix. -/
theorem eta_half_transform (γ : SL(2, ℤ)) (z : ℍ) :
    ModularForm.eta (γ • z : ℍ) = halfMultiplier γ * halfDenom γ z * ModularForm.eta z := by
  have h := (div_eq_iff (mul_ne_zero (halfDenom_ne_zero γ z)
    (ModularForm.eta_ne_zero z.im_pos))).mp (halfRatio_eq_multiplier γ z)
  simpa only [mul_assoc] using h

theorem halfMultiplier_sq (γ : SL(2, ℤ)) :
    halfMultiplier γ ^ 2 = Eta.etaMultiplier (Eta.etaExponent γ) :=
  halfRatio_sq γ UpperHalfPlane.I

/-- The half-weight multiplier is a twenty-fourth root of unity. -/
theorem halfMultiplier_pow_twentyFour (γ : SL(2, ℤ)) : halfMultiplier γ ^ 24 = 1 := by
  rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, halfMultiplier_sq]
  rw [← AddChar.map_nsmul_eq_pow]
  rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, AddChar.map_zero_eq_one]

theorem halfMultiplier_norm (γ : SL(2, ℤ)) : ‖halfMultiplier γ‖ = 1 := by
  have h := congrArg norm (halfMultiplier_sq γ)
  rw [norm_pow, show ‖Eta.etaMultiplier (Eta.etaExponent γ)‖ = 1 from
    (ZMod.toCircle _).norm_coe] at h
  nlinarith [norm_nonneg (halfMultiplier γ)]

theorem halfMultiplier_ne_zero (γ : SL(2, ℤ)) : halfMultiplier γ ≠ 0 := by
  rw [halfMultiplier]
  exact div_ne_zero (ModularForm.eta_ne_zero (γ • UpperHalfPlane.I).im_pos)
    (mul_ne_zero (halfDenom_ne_zero γ UpperHalfPlane.I)
      (ModularForm.eta_ne_zero UpperHalfPlane.I.im_pos))

@[simp] theorem halfMultiplier_one : halfMultiplier 1 = 1 := by
  rw [halfMultiplier]
  have hd : halfDenom (1 : SL(2, ℤ)) UpperHalfPlane.I = 1 := by
    unfold halfDenom
    rw [← Complex.sqrt_one]
    congr 1
    change (((1 : SL(2, ℤ)) 1 0 : ℤ) : ℂ) * (UpperHalfPlane.I : ℂ) +
      (((1 : SL(2, ℤ)) 1 1 : ℤ) : ℂ) = 1
    norm_num
  rw [hd, one_smul, one_mul]
  exact div_self (ModularForm.eta_ne_zero UpperHalfPlane.I.im_pos)

theorem halfMultiplier_T : halfMultiplier ModularGroup.T = translationCharacter 1 := by
  have hd : halfDenom ModularGroup.T UpperHalfPlane.I = 1 := by
    unfold halfDenom
    rw [← Complex.sqrt_one]
    congr 1
    change ((ModularGroup.T 1 0 : ℤ) : ℂ) * (UpperHalfPlane.I : ℂ) +
      ((ModularGroup.T 1 1 : ℤ) : ℂ) = 1
    norm_num [ModularGroup.T]
  have hT : ModularForm.eta (ModularGroup.T • UpperHalfPlane.I : ℍ) =
      translationCharacter 1 * ModularForm.eta UpperHalfPlane.I := by
    rw [modular_T_smul]
    simpa only [UpperHalfPlane.coe_vadd, Complex.ofReal_one, Nat.cast_one, add_comm] using
      eta_add_nat (UpperHalfPlane.I : ℂ) 1
  rw [halfMultiplier, hT, hd, one_mul]
  exact mul_div_cancel_right₀ _ (ModularForm.eta_ne_zero UpperHalfPlane.I.im_pos)

/-- The sign cocycle of the principal half-weight denominator. -/
def halfCocycle (γ δ : SL(2, ℤ)) : ℂ :=
  halfMultiplier (γ * δ) / (halfMultiplier γ * halfMultiplier δ)

theorem halfMultiplier_mul (γ δ : SL(2, ℤ)) :
    halfMultiplier (γ * δ) = halfMultiplier γ * halfMultiplier δ * halfCocycle γ δ := by
  rw [halfCocycle]
  field_simp [halfMultiplier_ne_zero γ, halfMultiplier_ne_zero δ]

/-- The cocycle compares the principal square roots in the denominator identity. -/
theorem halfDenom_mul (γ δ : SL(2, ℤ)) (z : ℍ) :
    halfCocycle γ δ * halfDenom (γ * δ) z = halfDenom γ (δ • z) * halfDenom δ z := by
  have h₁ := eta_half_transform (γ * δ) z
  have h₂ := eta_half_transform γ (δ • z)
  rw [mul_smul, h₂, eta_half_transform δ z] at h₁
  rw [halfMultiplier_mul] at h₁
  field_simp [halfMultiplier_ne_zero γ, halfMultiplier_ne_zero δ,
    ModularForm.eta_ne_zero z.im_pos] at h₁
  exact h₁.symm

theorem halfCocycle_sq (γ δ : SL(2, ℤ)) : halfCocycle γ δ ^ 2 = 1 := by
  rw [halfCocycle, div_pow, mul_pow]
  simp only [halfMultiplier_sq, Eta.etaExponent_mul, AddChar.map_add_eq_mul]
  exact div_self (mul_ne_zero (Eta.etaMultiplier_ne_zero _) (Eta.etaMultiplier_ne_zero _))

/-- The square-root discrepancy is a sign, as required by the half-weight cocycle. -/
theorem halfCocycle_eq_one_or_neg_one (γ δ : SL(2, ℤ)) :
    halfCocycle γ δ = 1 ∨ halfCocycle γ δ = -1 :=
  sq_eq_one_iff.mp (halfCocycle_sq γ δ)

theorem halfMultiplier_S : halfMultiplier ModularGroup.S = (Complex.sqrt Complex.I)⁻¹ := by
  have hS : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [modular_S_smul]
    ext
    norm_num [Complex.inv_I]
  have hd : halfDenom ModularGroup.S UpperHalfPlane.I = Complex.sqrt Complex.I := by
    unfold halfDenom
    rw [ModularGroup.denom_S]
    rfl
  rw [halfMultiplier, hS, hd]
  rw [mul_comm (Complex.sqrt Complex.I), div_mul_eq_div_div,
    div_self (ModularForm.eta_ne_zero UpperHalfPlane.I.im_pos), one_div]

theorem eta_dilate_half_transform {N m : ℕ} (hm : m ∈ N.divisors)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    ModularForm.eta ((m : ℂ) * (γ • z : ℍ)) =
      halfMultiplier (divisorConjugate N γ hγ m hm) * halfDenom γ z *
        ModularForm.eta ((m : ℂ) * (z : ℂ)) := by
  have hmpos := Nat.pos_of_mem_divisors hm
  have hmem := mem_Gamma0_divisor (Nat.dvd_of_mem_divisors hm) γ hγ
  change ModularForm.eta (Eta.dilate m (by exact_mod_cast hmpos) (γ • z)) = _
  rw [Eta.dilate_smul m hmpos γ hmem, eta_half_transform]
  simp only [halfDenom, Eta.denom_levelConjugate m hmpos γ hmem z]
  rfl

private theorem prod_const_zpow {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (a : ℂ) (ha : a ≠ 0) : (∏ i ∈ s, a ^ f i) = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ ha]

/-- The unsquared transformation is the finite product of the actual eta multipliers. -/
theorem transform_eq_prod_halfMultiplier {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    etaQuotient N r (γ • z) =
      (∏ m ∈ N.divisors.attach,
        halfMultiplier (divisorConjugate N γ hγ m m.property) ^ exponent r m) *
        denom γ z ^ k * etaQuotient N r z := by
  rw [etaQuotient, ← Finset.prod_attach N.divisors]
  have hfactor (m : {m // m ∈ N.divisors}) := eta_dilate_half_transform m.property γ hγ z
  simp_rw [hfactor, mul_zpow]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_const_zpow _ _ _ (halfDenom_ne_zero γ z)]
  simp only [Finset.sum_attach]
  change _ * halfDenom γ z ^ exponentSum N r * _ = _
  rw [hk, zpow_mul, zpow_ofNat, halfDenom_sq]
  congr 1
  exact Finset.prod_attach N.divisors
    (fun m : ℕ ↦ ModularForm.eta ((m : ℂ) * (z : ℂ)) ^ exponent r m)

/-- Finite-product reduction used in the arithmetic character calculation. -/
theorem slashMultiplier_eq_prod_halfMultiplier {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    slashMultiplier N r k γ = ∏ m ∈ N.divisors.attach,
      halfMultiplier (divisorConjugate N γ hγ m m.property) ^ exponent r m := by
  rw [slashMultiplier, ModularForm.SL_slash_apply, transform_eq_prod_halfMultiplier hk γ hγ]
  simp only [zpow_neg]
  field_simp [ne_zero N r UpperHalfPlane.I, denom_ne_zero γ UpperHalfPlane.I]
  exact mul_div_cancel_right₀ _ (zpow_ne_zero k (denom_ne_zero γ UpperHalfPlane.I))

end WeightTwoCusps.EtaQuotient
