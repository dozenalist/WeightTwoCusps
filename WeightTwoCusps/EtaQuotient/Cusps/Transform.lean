module

public import WeightTwoCusps.EtaQuotient.Transformation.Reflection
public import WeightTwoCusps.EtaQuotient.Transformation.Basic
public import WeightTwoCusps.EtaQuotient.Cusps.Arithmetic
public import WeightTwoCusps.EtaQuotient.Cusps.Product

/-!
# Dilation at arbitrary rational cusps

An integral dilation followed by an integral modular transformation can be
factored into another integral modular transformation and a positive affine
map. Its slope is `gcd(c, m)² / m`. This is the local calculation needed for
the general Ligozat cusp inequalities, including negative exponents.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Topology Real

namespace WeightTwoCusps.EtaQuotient

/-- The positive common factor removed from the first column after dilation. -/
def cuspGcd (m : ℕ) (γ : SL(2, ℤ)) : ℕ := Nat.gcd (γ 1 0).natAbs m

theorem cuspGcd_pos {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) : 0 < cuspGcd m γ :=
  Nat.gcd_pos_of_pos_right _ hm

/-- An integral matrix factorization of `diag(m,1) * γ`.
The right factor is upper triangular, with positive diagonal entries. -/
theorem exists_cusp_factorization {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    ∃ (δ : SL(2, ℤ)) (b e : ℤ), 0 < e ∧
      (m : ℤ) * γ 0 0 = δ 0 0 * cuspGcd m γ ∧
      γ 1 0 = δ 1 0 * cuspGcd m γ ∧
      (m : ℤ) * γ 0 1 = δ 0 0 * b + δ 0 1 * e ∧
      γ 1 1 = δ 1 0 * b + δ 1 1 * e ∧
      (cuspGcd m γ : ℤ) * e = m := by
  have hcop : Int.gcd (γ 0 0) (γ 1 0) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (γ.isCoprime_col 0)
  have hgcd : Int.gcd ((m : ℤ) * γ 0 0) (γ 1 0) = cuspGcd m γ := by
    rw [Int.gcd_mul_left_left_of_gcd_eq_one hcop]
    simp [cuspGcd, Int.gcd_def, Nat.gcd_comm]
  obtain ⟨a, c, hac, ha, hc⟩ := Int.exists_gcd_one (hgcd.symm ▸ cuspGcd_pos hm γ)
  rw [hgcd] at ha hc
  obtain ⟨δ, hδa, hδc⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr hac).exists_SL2_col 0
  let b : ℤ := δ 1 1 * ((m : ℤ) * γ 0 1) - δ 0 1 * γ 1 1
  let e : ℤ := δ 0 0 * γ 1 1 - δ 1 0 * ((m : ℤ) * γ 0 1)
  have hd : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using δ.det_coe
  have hγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have ha' : (m : ℤ) * γ 0 0 = δ 0 0 * cuspGcd m γ := by simpa [hδa] using ha
  have hc' : γ 1 0 = δ 1 0 * cuspGcd m γ := by simpa [hδc] using hc
  have hge : (cuspGcd m γ : ℤ) * e = m := by
    dsimp [e]
    linear_combination -(γ 1 1) * ha' + (m : ℤ) * γ 0 1 * hc' + (m : ℤ) * hγ
  have he : 0 < e := by
    have hg : (0 : ℤ) < cuspGcd m γ := by exact_mod_cast cuspGcd_pos hm γ
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    nlinarith
  refine ⟨δ, b, e, he, ha', hc', ?_, ?_, hge⟩
  · dsimp [b, e]
    linear_combination -((m : ℤ) * γ 0 1) * hd
  · dsimp [b, e]
    linear_combination -(γ 1 1) * hd

/-- A positive affine map on the upper half-plane. -/
def cuspAffine (a : ℝ) (ha : 0 < a) (b : ℝ) (z : ℍ) : ℍ :=
  b +ᵥ Eta.dilate a ha z

@[simp] theorem coe_cuspAffine (a : ℝ) (ha : 0 < a) (b : ℝ) (z : ℍ) :
    (cuspAffine a ha b z : ℂ) = (b : ℂ) + (a : ℂ) * (z : ℂ) := rfl

theorem tendsto_cuspAffine (a : ℝ) (ha : 0 < a) (b : ℝ) :
    Tendsto (cuspAffine a ha b) atImInfty atImInfty := by
  change Tendsto _ atImInfty (comap UpperHalfPlane.im atTop)
  rw [tendsto_comap_iff]
  simpa [cuspAffine, Eta.dilate, Function.comp_def] using
    (Filter.tendsto_comap.const_mul_atTop ha :
      Tendsto (fun z : ℍ ↦ a * z.im) atImInfty atTop)

/-- The affine factorization gives the exact eta-square slash formula.
The multiplier has absolute value `g / m`, and the slope is `g² / m`. -/
theorem etaSq_dilate_slash_eq_affine {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    ∃ (a : ℝ) (ha : 0 < a) (b : ℝ) (u : ℂ),
      a = (cuspGcd m γ : ℝ) ^ 2 / m ∧
      ‖u‖ = (cuspGcd m γ : ℝ) / m ∧
      ((fun z : ℍ ↦ ModularForm.eta ((m : ℂ) * (z : ℂ)) ^ 2) ∣[(1 : ℤ)] γ) =
        fun z ↦ u * ModularForm.eta (cuspAffine a ha b z) ^ 2 := by
  obtain ⟨δ, b, e, he, hma, hc, hmb, hd, hge⟩ := exists_cusp_factorization hm γ
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hgR : (0 : ℝ) < cuspGcd m γ := by exact_mod_cast cuspGcd_pos hm γ
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hgeR : (cuspGcd m γ : ℝ) * e = m := by exact_mod_cast hge
  let a : ℝ := cuspGcd m γ / e
  have ha : 0 < a := div_pos hgR heR
  let t : ℝ := b / e
  let w (z : ℍ) := cuspAffine a ha t z
  have hw (z : ℍ) : (w z : ℂ) = ((cuspGcd m γ : ℂ) * (z : ℂ) + b) / e := by
    simp only [w, coe_cuspAffine, t, a, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_natCast]
    ring
  have hmaC : (m : ℂ) * (γ 0 0 : ℂ) = (δ 0 0 : ℂ) * cuspGcd m γ := by exact_mod_cast hma
  have hcC : (γ 1 0 : ℂ) = (δ 1 0 : ℂ) * cuspGcd m γ := by exact_mod_cast hc
  have hmbC : (m : ℂ) * (γ 0 1 : ℂ) = (δ 0 0 : ℂ) * b + (δ 0 1 : ℂ) * e := by
    exact_mod_cast hmb
  have hdC : (γ 1 1 : ℂ) = (δ 1 0 : ℂ) * b + (δ 1 1 : ℂ) * e := by exact_mod_cast hd
  have hden (z : ℍ) : denom δ (w z) = denom γ z / (e : ℂ) := by
    change (δ 1 0 : ℂ) * (w z : ℂ) + (δ 1 1 : ℂ) =
      ((γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)) / e
    rw [hw, hcC, hdC]
    field_simp
    ring
  have harg (z : ℍ) : ((m : ℂ) * (γ • z : ℍ)) = (δ • w z : ℍ) := by
    rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
    change (m : ℂ) * (((γ 0 0 : ℂ) * (z : ℂ) + γ 0 1) / denom γ z) =
      ((δ 0 0 : ℂ) * (w z : ℂ) + δ 0 1) / denom δ (w z)
    rw [hden, hw]
    field_simp [denom_ne_zero γ z]
    linear_combination (z : ℂ) * hmaC + hmbC
  refine ⟨a, ha, t, Eta.etaMultiplier (Eta.etaExponent δ) / e, ?_, ?_, ?_⟩
  · dsimp [a]
    field_simp
    nlinarith
  · rw [norm_div, show ‖Eta.etaMultiplier (Eta.etaExponent δ)‖ = 1 from
      (ZMod.toCircle _).norm_coe]
    simp only [Complex.norm_intCast, abs_of_pos heR]
    field_simp
    linarith
  · ext z
    rw [ModularForm.SL_slash_apply, harg]
    change Eta.etaSq (δ • w z) * denom γ z ^ (-1 : ℤ) = _
    rw [Eta.etaSq_modular_transform, hden]
    simp only [Eta.etaSq, Int.reduceNeg, zpow_neg_one]
    field_simp [denom_ne_zero γ z]
    rfl

/-- The rational slope of the affine coordinate at a cusp. -/
def cuspSlope (m : ℕ) (γ : SL(2, ℤ)) : ℚ := (cuspGcd m γ : ℚ) ^ 2 / m

theorem cuspSlope_pos {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) : 0 < cuspSlope m γ := by
  have hg := cuspGcd_pos hm γ
  dsimp [cuspSlope]
  positivity

private theorem etaSq_eq_exp_eulerPart (z : ℍ) :
    ModularForm.eta z ^ 2 =
      Complex.exp (2 * π * I * (z : ℂ) / 12) * eulerPart z ^ 2 := by
  simp only [ModularForm.eta, eulerPart, mul_pow, Function.Periodic.qParam,
    Complex.ofReal_ofNat, ← Complex.exp_nat_mul]
  congr 2
  ring

/-- Removing the expected leading exponential leaves a nonzero limit for
each dilated eta-square factor at every cusp. -/
theorem etaSq_cusp_leading_limit {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    ∃ u : ℂ, u ≠ 0 ∧ Tendsto
      (fun z : ℍ ↦ Complex.exp (-(2 * π * I * (z : ℂ) * (cuspSlope m γ : ℂ) / 12)) *
        (((fun w : ℍ ↦ ModularForm.eta ((m : ℂ) * (w : ℂ)) ^ 2) ∣[(1 : ℤ)] γ) z))
      atImInfty (𝓝 u) := by
  obtain ⟨a, ha, b, u, hslope, hnorm, hfun⟩ := etaSq_dilate_slash_eq_affine hm γ
  have hu : u ≠ 0 := by
    rw [← norm_ne_zero_iff, hnorm]
    exact ne_of_gt (div_pos (by exact_mod_cast cuspGcd_pos hm γ)
      (by exact_mod_cast hm))
  have hs : (cuspSlope m γ : ℂ) = (a : ℂ) := by
    rw [hslope]
    simp [cuspSlope, Rat.cast_div, Rat.cast_pow]
  have heuler : Tendsto (fun z : ℍ ↦ eulerPart (z : ℂ)) atImInfty (𝓝 1) := by
    simpa using eulerPart_dilate_tendsto_one (m := 1) (by norm_num)
  have ht := ((heuler.comp (tendsto_cuspAffine a ha b)).pow 2).const_mul
    (u * Complex.exp (2 * π * I * (b : ℂ) / 12))
  simp only [one_pow, mul_one] at ht
  refine ⟨u * Complex.exp (2 * π * I * (b : ℂ) / 12),
    mul_ne_zero hu (Complex.exp_ne_zero _), ?_⟩
  apply ht.congr
  intro z
  rw [hfun]
  dsimp only [Function.comp_def]
  rw [etaSq_eq_exp_eulerPart, coe_cuspAffine, hs]
  have he : Complex.exp (-(2 * π * I * (z : ℂ) * (a : ℂ) / 12)) *
      Complex.exp (2 * π * I * ((b : ℂ) + (a : ℂ) * (z : ℂ)) / 12) =
      Complex.exp (2 * π * I * (b : ℂ) / 12) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [← he]
  ring

/-- The slashed doubled quotient after removing its leading cusp exponential. -/
def cuspUnit (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ)) (z : ℍ) : ℂ :=
  Complex.exp (-(2 * π * I * (z : ℂ) * (cuspSum N r (γ 1 0).natAbs : ℂ) / 12)) *
    ((etaQuotient N (double r) ∣[exponentSum N r] γ) z)

theorem cuspUnit_eq_prod (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ)) (z : ℍ) :
    cuspUnit N r γ z = ∏ m ∈ N.divisors,
      (Complex.exp (-(2 * π * I * (z : ℂ) * (cuspSlope m γ : ℂ) / 12)) *
        (((fun w : ℍ ↦ ModularForm.eta ((m : ℂ) * (w : ℂ)) ^ 2) ∣[(1 : ℤ)] γ) z)) ^
          exponent r m := by
  rw [cuspUnit, double_slash_eq_prod]
  dsimp only
  symm
  simp_rw [mul_zpow, ← Complex.exp_int_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  congr 1
  have hs : (cuspSum N r (γ 1 0).natAbs : ℂ) =
      ∑ m ∈ N.divisors, (cuspSlope m γ : ℂ) * (exponent r m : ℂ) := by
    simp [cuspSum, cuspSlope, cuspGcd]
  rw [hs]
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The normalized cusp factor has a nonzero limit, even with negative exponents. -/
theorem cuspUnit_tendsto_nonzero (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ)) :
    ∃ u : ℂ, u ≠ 0 ∧ Tendsto (cuspUnit N r γ) atImInfty (𝓝 u) := by
  choose u hu ht using fun m : {m // m ∈ N.divisors} ↦
    etaSq_cusp_leading_limit (Nat.pos_of_mem_divisors m.property) γ
  refine ⟨∏ m ∈ N.divisors.attach, u m ^ exponent r m,
    Finset.prod_ne_zero_iff.mpr (fun m _ ↦ zpow_ne_zero _ (hu m)), ?_⟩
  have hlim := tendsto_finsetProd N.divisors.attach (fun m _ ↦
    (ht m).zpow₀ (exponent r m) (Or.inl (hu m)))
  apply hlim.congr
  intro z
  rw [cuspUnit_eq_prod]
  exact Finset.prod_attach N.divisors (fun m : ℕ ↦
    (Complex.exp (-(2 * π * I * (z : ℂ) * (cuspSlope m γ : ℂ) / 12)) *
      (((fun w : ℍ ↦ ModularForm.eta ((m : ℂ) * (w : ℂ)) ^ 2) ∣[(1 : ℤ)] γ) z)) ^
        exponent r m)

theorem double_slash_eq_exp_mul_cuspUnit (N : ℕ) (r : Fin N → ℤ)
    (γ : SL(2, ℤ)) (z : ℍ) :
    (etaQuotient N (double r) ∣[exponentSum N r] γ) z =
      Complex.exp (2 * π * I * (z : ℂ) * (cuspSum N r (γ 1 0).natAbs : ℂ) / 12) *
        cuspUnit N r γ z := by
  rw [cuspUnit, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem norm_double_slash_eq_exp_mul_cuspUnit (N : ℕ) (r : Fin N → ℤ)
    (γ : SL(2, ℤ)) (z : ℍ) :
    ‖(etaQuotient N (double r) ∣[exponentSum N r] γ) z‖ =
      Real.exp ((-2 * π * (cuspSum N r (γ 1 0).natAbs : ℝ) / 12) * z.im) *
        ‖cuspUnit N r γ z‖ := by
  rw [double_slash_eq_exp_mul_cuspUnit, norm_mul, Complex.norm_exp]
  congr 2
  simp only [div_ofNat_re, mul_re, mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Complex.ratCast_re,
    Complex.ratCast_im, zero_mul, mul_zero, add_zero, zero_add, mul_one, sub_zero,
    zero_sub, UpperHalfPlane.coe_im]
  ring

private theorem exp_cusp_tendsto_zero {s : ℚ} (hs : 0 < s) :
    Tendsto (fun z : ℍ ↦ Complex.exp (2 * π * I * (z : ℂ) * (s : ℂ) / 12))
      atImInfty (𝓝 0) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hperiod : (0 : ℝ) < 12 / (s : ℝ) := by positivity
  have heq : (fun z : ℍ ↦ Complex.exp (2 * π * I * (z : ℂ) * (s : ℂ) / 12)) =
      (fun z : ℍ ↦ Function.Periodic.qParam (12 / (s : ℝ)) z) := by
    funext z
    simp only [Function.Periodic.qParam, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.ofReal_ratCast]
    congr 1
    field_simp
  rw [heq]
  exact qParam_tendsto_atImInfty hperiod

/-- The strict Ligozat inequality suffices for vanishing at an arbitrary cusp. -/
theorem double_slash_isZero_of_cuspSum_pos {N : ℕ} {r : Fin N → ℤ} (γ : SL(2, ℤ))
    (h : 0 < cuspSum N r (γ 1 0).natAbs) :
    IsZeroAtImInfty (etaQuotient N (double r) ∣[exponentSum N r] γ) := by
  obtain ⟨u, _, hu⟩ := cuspUnit_tendsto_nonzero N r γ
  have ht := (exp_cusp_tendsto_zero h).mul hu
  rw [zero_mul] at ht
  exact ht.congr (fun z ↦ (double_slash_eq_exp_mul_cuspUnit N r γ z).symm)

/-- Zero Ligozat sum gives a nonzero finite limit in the slashed coordinate. -/
theorem double_slash_tendsto_nonzero_of_cuspSum_zero {N : ℕ} {r : Fin N → ℤ}
    (γ : SL(2, ℤ)) (h : cuspSum N r (γ 1 0).natAbs = 0) :
    ∃ u : ℂ, u ≠ 0 ∧ Tendsto
      (etaQuotient N (double r) ∣[exponentSum N r] γ) atImInfty (𝓝 u) := by
  obtain ⟨u, hu, ht⟩ := cuspUnit_tendsto_nonzero N r γ
  refine ⟨u, hu, ht.congr (fun z ↦ ?_)⟩
  simp [cuspUnit, h]

/-- Weak Ligozat inequalities suffice for boundedness, allowing arbitrary cancellation. -/
theorem double_slash_isBounded_of_cuspSum_nonneg {N : ℕ} {r : Fin N → ℤ}
    (γ : SL(2, ℤ)) (h : 0 ≤ cuspSum N r (γ 1 0).natAbs) :
    IsBoundedAtImInfty (etaQuotient N (double r) ∣[exponentSum N r] γ) := by
  rcases h.eq_or_lt with heq | hpos
  · obtain ⟨u, _, ht⟩ := double_slash_tendsto_nonzero_of_cuspSum_zero γ heq.symm
    exact ht.isBigO_one ℝ
  · exact (double_slash_isZero_of_cuspSum_pos γ hpos).boundedAtFilter

/-- A negative cusp sum forces the slashed quotient's magnitude to diverge. -/
theorem norm_double_slash_tendsto_atTop_of_cuspSum_neg {N : ℕ} {r : Fin N → ℤ}
    (γ : SL(2, ℤ)) (h : cuspSum N r (γ 1 0).natAbs < 0) :
    Tendsto (fun z : ℍ ↦ ‖(etaQuotient N (double r) ∣[exponentSum N r] γ) z‖)
      atImInfty atTop := by
  obtain ⟨u, hu, ht⟩ := cuspUnit_tendsto_nonzero N r γ
  have hs : (cuspSum N r (γ 1 0).natAbs : ℝ) < 0 := by exact_mod_cast h
  have hc : 0 < -2 * π * (cuspSum N r (γ 1 0).natAbs : ℝ) / 12 := by
    rw [show -2 * π * (cuspSum N r (γ 1 0).natAbs : ℝ) / 12 =
      (2 * π * -(cuspSum N r (γ 1 0).natAbs : ℝ)) / 12 by ring]
    exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
      (neg_pos.mpr hs)) (by norm_num)
  have hi : Tendsto (fun z : ℍ ↦ z.im) atImInfty atTop := Filter.tendsto_comap
  have he := Real.tendsto_exp_atTop.comp (hi.const_mul_atTop hc)
  have hlim := he.atTop_mul_pos (norm_pos_iff.mpr hu) ht.norm
  exact hlim.congr (fun z ↦ (norm_double_slash_eq_exp_mul_cuspUnit N r γ z).symm)

/-- Ligozat's boundedness criterion at every rational cusp, for doubled exponents. -/
theorem double_slash_isBounded_iff (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (etaQuotient N (double r) ∣[exponentSum N r] γ) ↔
      0 ≤ cuspSum N r (γ 1 0).natAbs := by
  refine ⟨fun h ↦ ?_, double_slash_isBounded_of_cuspSum_nonneg γ⟩
  by_contra hn
  have ht := norm_double_slash_tendsto_atTop_of_cuspSum_neg γ (lt_of_not_ge hn)
  exact Filter.not_isBoundedUnder_of_tendsto_atTop ht
    ((Asymptotics.isBigO_one_iff ℝ).mp h)

/-- Ligozat's vanishing criterion at every rational cusp, for doubled exponents. -/
theorem double_slash_isZero_iff (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (etaQuotient N (double r) ∣[exponentSum N r] γ) ↔
      0 < cuspSum N r (γ 1 0).natAbs := by
  refine ⟨fun h ↦ ?_, double_slash_isZero_of_cuspSum_pos γ⟩
  have hn := (double_slash_isBounded_iff N r γ).mp h.boundedAtFilter
  rcases hn.eq_or_lt with heq | hpos
  · obtain ⟨u, hu, ht⟩ := double_slash_tendsto_nonzero_of_cuspSum_zero γ heq.symm
    exact False.elim (hu (tendsto_nhds_unique ht h))
  · exact hpos

/-- Squaring the weight-`k` slash gives the doubled quotient's expected-weight slash. -/
theorem double_slash_eq_square {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ)) :
    etaQuotient N (double r) ∣[exponentSum N r] γ =
      fun z ↦ ((etaQuotient N r ∣[k] γ) z) ^ 2 := by
  ext z
  simp only [ModularForm.SL_slash_apply, double_apply, mul_pow]
  rw [show -exponentSum N r = (-k) * 2 by rw [hk]; ring,
    zpow_mul, zpow_ofNat]

/-- The analytic Ligozat boundedness criterion, with arbitrary integer exponents. -/
theorem slash_isBounded_iff {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (etaQuotient N r ∣[k] γ) ↔
      0 ≤ cuspSum N r (γ 1 0).natAbs := by
  rw [← double_slash_isBounded_iff N r γ, double_slash_eq_square hk γ]
  change ((etaQuotient N r ∣[k] γ) =O[atImInfty] (1 : ℍ → ℝ)) ↔
    ((fun z ↦ ((etaQuotient N r ∣[k] γ) z) ^ 2) =O[atImInfty] (1 : ℍ → ℝ))
  constructor
  · intro h
    convert! h.pow 2 using 1
    ext z
    simp
  · intro h
    apply Asymptotics.IsBigO.of_pow (n := 2) (by norm_num)
    convert! h using 1
    ext z
    simp

/-- The analytic Ligozat vanishing criterion, with arbitrary integer exponents. -/
theorem slash_isZero_iff {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (etaQuotient N r ∣[k] γ) ↔
      0 < cuspSum N r (γ 1 0).natAbs := by
  rw [← double_slash_isZero_iff N r γ, double_slash_eq_square hk γ]
  change (Tendsto (etaQuotient N r ∣[k] γ) atImInfty (𝓝 0)) ↔
    (Tendsto (fun z ↦ ((etaQuotient N r ∣[k] γ) z) ^ 2) atImInfty (𝓝 0))
  constructor
  · intro h
    simpa only [Pi.pow_apply, zero_pow (by norm_num : 2 ≠ 0)] using h.pow 2
  · intro h
    rw [← Asymptotics.isLittleO_one_iff (F := ℝ)] at h ⊢
    apply Asymptotics.IsLittleO.of_pow (n := 2) ?_ (by norm_num)
    convert! h using 1
    ext z
    simp

/-- The finite weak inequalities characterize boundedness after every integral slash. -/
theorem holomorphicAtCusps_iff_slash_isBounded {N : ℕ} (hN : 0 < N)
    {r : Fin N → ℤ} {k : ℤ} (hk : HasWeight N r k) :
    HolomorphicAtCusps N r ↔ ∀ γ : SL(2, ℤ),
      IsBoundedAtImInfty (etaQuotient N r ∣[k] γ) := by
  constructor
  · intro h γ
    exact (slash_isBounded_iff hk γ).mpr
      ((holomorphicAtCusps_iff_all_denominators hN r).mp h _)
  · intro h c _
    let γ : SL(2, ℤ) := ⟨!![1, 0; (c : ℤ), 1], by simp⟩
    simpa [γ] using (slash_isBounded_iff hk γ).mp (h γ)

/-- The finite strict inequalities characterize vanishing after every integral slash. -/
theorem vanishingAtCusps_iff_slash_isZero {N : ℕ} (hN : 0 < N)
    {r : Fin N → ℤ} {k : ℤ} (hk : HasWeight N r k) :
    VanishingAtCusps N r ↔ ∀ γ : SL(2, ℤ),
      IsZeroAtImInfty (etaQuotient N r ∣[k] γ) := by
  constructor
  · intro h γ
    exact (slash_isZero_iff hk γ).mpr
      ((vanishingAtCusps_iff_all_denominators hN r).mp h _)
  · intro h c _
    let γ : SL(2, ℤ) := ⟨!![1, 0; (c : ℤ), 1], by simp⟩
    simpa [γ] using (slash_isZero_iff hk γ).mp (h γ)

/-- The Ligozat inequalities give Mathlib's analytic cusp boundedness condition. -/
theorem bounded_at_cusps_of_holomorphicAtCusps {N : ℕ} (hN : 0 < N)
    {r : Fin N → ℤ} {k : ℤ} (hk : HasWeight N r k) (h : HolomorphicAtCusps N r)
    {c : OnePoint ℝ} (hc : IsCusp c (CongruenceSubgroup.Gamma0 N)) :
    c.IsBoundedAt (etaQuotient N r) k := by
  have : NeZero N := ⟨hN.ne'⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  intro γ _
  exact (holomorphicAtCusps_iff_slash_isBounded hN hk).mp h γ

/-- Strict Ligozat inequalities give Mathlib's analytic cusp vanishing condition. -/
theorem zero_at_cusps_of_vanishingAtCusps {N : ℕ} (hN : 0 < N)
    {r : Fin N → ℤ} {k : ℤ} (hk : HasWeight N r k) (h : VanishingAtCusps N r)
    {c : OnePoint ℝ} (hc : IsCusp c (CongruenceSubgroup.Gamma0 N)) :
    c.IsZeroAt (etaQuotient N r) k := by
  have : NeZero N := ⟨hN.ne'⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  exact (vanishingAtCusps_iff_slash_isZero hN hk).mp h γ

end WeightTwoCusps.EtaQuotient
