module

public import WeightTwoCusps.EtaQuotient.QExpansion.Basic
public import WeightTwoCusps.EtaQuotient.QExpansion.Sequence

/-! # Euler coefficients in normalized eta-quotient expansions -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Function Complex Filter
open UpperHalfPlane hiding I
open scoped Topology Manifold ModularForm Real MatrixGroups

namespace WeightTwoCusps.EtaQuotient

/-- A single normalized dilated eta factor, to an arbitrary integer power. -/
def eulerFactorPower (m : ℕ) (n : ℤ) (z : ℍ) : ℂ :=
  eulerPart ((m : ℂ) * (z : ℂ)) ^ n

theorem eulerFactor_ne_zero {m : ℕ} (hm : 0 < m) (z : ℍ) :
    eulerPart ((m : ℂ) * (z : ℂ)) ≠ 0 := by
  apply ModularForm.eta_tprod_ne_zero
  simpa using mul_pos (show (0 : ℝ) < m by exact_mod_cast hm) z.im_pos

theorem eulerFactorPower_periodic (m : ℕ) (n : ℤ) :
    Periodic (eulerFactorPower m n ∘ UpperHalfPlane.ofComplex) 1 := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro z
  simp only [eulerFactorPower, UpperHalfPlane.coe_vadd, Complex.ofReal_one, mul_add, mul_one]
  rw [add_comm (m : ℂ), eulerPart_add_nat]

theorem eulerFactorPower_holo {m : ℕ} (hm : 0 < m) (n : ℤ) :
    MDiff (eulerFactorPower m n) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := fun z : ℂ ↦ eulerPart ((m : ℂ) * z) ^ n) ?_ ?_
  · intro z hz
    have hpos : 0 < (((m : ℂ) * z).im) := by
      simpa using mul_pos (show (0 : ℝ) < m by exact_mod_cast hm) hz
    exact (((ModularForm.differentiableAt_eta_tprod hpos).comp z
      ((differentiableAt_const (m : ℂ)).mul differentiableAt_id)).zpow
        (Or.inl (ModularForm.eta_tprod_ne_zero hpos))).differentiableWithinAt
  · intro z hz
    simp [eulerFactorPower, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem eulerFactorPower_tendsto_one {m : ℕ} (hm : 0 < m) (n : ℤ) :
    Tendsto (eulerFactorPower m n) atImInfty (𝓝 1) := by
  convert! (eulerPart_dilate_tendsto_one hm).zpow₀ n (Or.inl one_ne_zero) using 1
  simp

theorem eulerFactorPower_analytic {m : ℕ} (hm : 0 < m) (n : ℤ) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (eulerFactorPower m n)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num) (eulerFactorPower_periodic m n)
    (eulerFactorPower_holo hm n) ((eulerFactorPower_tendsto_one hm n).isBigO_one ℝ)

theorem eulerFactorPower_coeff_zero {m : ℕ} (hm : 0 < m) (n : ℤ) :
    (UpperHalfPlane.qExpansion 1 (eulerFactorPower m n)).coeff 0 = 1 := by
  rw [UpperHalfPlane.qExpansion_coeff_zero (by norm_num) (eulerFactorPower_analytic hm n)
    (eulerFactorPower_periodic m n)]
  exact (eulerFactorPower_tendsto_one hm n).limUnder_eq

private theorem qParam_dilate (m : ℕ) (z : ℍ) :
    Periodic.qParam 1 ((m : ℂ) * (z : ℂ)) = Periodic.qParam 1 z ^ m := by
  simp only [Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Euler's pentagonal coefficients give the entire q-expansion of one normalized eta factor. -/
theorem qExpansion_eulerFactor_coeff {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (eulerFactorPower m 1)).coeff n =
      (dilateCoefficient m eulerCoefficient n : ℂ) := by
  let : FunLike (ℍ → ℂ) ℍ ℂ := { coe := id, coe_injective := Function.injective_id }
  symm
  have hsum (z : ℍ) : HasSum (fun j ↦ (dilateCoefficient m eulerCoefficient j : ℂ) *
      Periodic.qParam 1 z ^ j) (eulerFactorPower m 1 z) := by
    have hq : ‖Periodic.qParam 1 z‖ < 1 := Periodic.norm_qParam_lt_one (by norm_num) z.im_pos
    have hqm : ‖Periodic.qParam 1 z ^ m‖ < 1 := by
      simpa only [norm_pow] using pow_lt_one₀ (norm_nonneg _) hq hm.ne'
    have hs := hasSum_dilateCoefficient m hm (hasSum_eulerCoefficient hqm)
    rw [eulerFunction_eq_tprod hqm] at hs
    convert hs using 1
    simp only [eulerFactorPower, zpow_one, eulerPart, ModularForm.eta_q, qParam_dilate]
  have ht := UpperHalfPlane.qExpansion_coeff_unique (h := 1) (eulerFactorPower m 1) (by norm_num)
    (eulerFactorPower_analytic hm 1)
    (c := fun j ↦ (dilateCoefficient m eulerCoefficient j : ℂ))
    (fun z ↦ by convert hsum z using 1; rfl) n
  convert ht using 1
  rfl

private def eulerFirstCoefficient {m : ℕ} (hm : 0 < m) : ℤ →+ ℂ where
  toFun n := (UpperHalfPlane.qExpansion 1 (eulerFactorPower m n)).coeff 1
  map_zero' := by
    rw [show eulerFactorPower m 0 = (1 : ℍ → ℂ) by ext z; simp [eulerFactorPower],
      UpperHalfPlane.qExpansion_one]
    simp
  map_add' a b := by
    have heq : eulerFactorPower m (a + b) = eulerFactorPower m a * eulerFactorPower m b := by
      ext z
      exact zpow_add₀ (eulerFactor_ne_zero hm z) a b
    rw [heq, UpperHalfPlane.qExpansion_mul (eulerFactorPower_analytic hm a)
      (eulerFactorPower_analytic hm b), PowerSeries.coeff_one_mul]
    simp only [← PowerSeries.coeff_zero_eq_constantCoeff, eulerFactorPower_coeff_zero hm,
      mul_one]

/-- Integer powers act linearly on the first normalized coefficient. -/
theorem qExpansion_eulerFactorPower_coeff_one {m : ℕ} (hm : 0 < m) (n : ℤ) :
    (UpperHalfPlane.qExpansion 1 (eulerFactorPower m n)).coeff 1 =
      if m = 1 then -(n : ℂ) else 0 := by
  have h := (eulerFirstCoefficient hm).map_zsmul n (1 : ℤ)
  change (eulerFirstCoefficient hm) (n • (1 : ℤ)) = _ at h
  simp only [zsmul_eq_mul, mul_one] at h
  change (UpperHalfPlane.qExpansion 1 (eulerFactorPower m n)).coeff 1 =
    (n : ℂ) * (UpperHalfPlane.qExpansion 1 (eulerFactorPower m 1)).coeff 1 at h
  rw [h, qExpansion_eulerFactor_coeff hm]
  by_cases hm1 : m = 1
  · subst m
    have hec : eulerCoefficient 1 = -1 := by
      norm_num [eulerCoefficient,
        show Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} by decide, pentagonal_def]
    simp [dilateCoefficient, hec]
  · have hmd : ¬m ∣ 1 := by simpa using hm1
    simp [dilateCoefficient, hmd, hm1]

theorem analytic_cusp_prod {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (hA : ∀ i ∈ s, AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (f i)) 0) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (fun z ↦ ∏ i ∈ s, f i z)) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num)
      (by intro z; rfl) mdifferentiable_const
      ((show Tendsto (fun _ : ℍ ↦ (1 : ℂ)) atImInfty (𝓝 1) from tendsto_const_nhds).isBigO_one ℝ)
  | @insert a s ha ih =>
    have haA := hA a (Finset.mem_insert_self _ _)
    have hsA := ih (fun i hi ↦ hA i (Finset.mem_insert_of_mem hi))
    have heq : (fun z ↦ ∏ i ∈ insert a s, f i z) = f a * (fun z ↦ ∏ i ∈ s, f i z) := by
      ext z
      simp [ha]
    rw [heq, UpperHalfPlane.cuspFunction_mul haA.continuousAt hsA.continuousAt]
    exact haA.mul hsA

theorem qExpansion_prod {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (hA : ∀ i ∈ s, AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (f i)) 0) :
    UpperHalfPlane.qExpansion 1 (fun z ↦ ∏ i ∈ s, f i z) =
      ∏ i ∈ s, UpperHalfPlane.qExpansion 1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [show (fun _ : ℍ ↦ (1 : ℂ)) = (1 : ℍ → ℂ) by ext z; rfl,
      UpperHalfPlane.qExpansion_one]
  | @insert a s ha ih =>
    have hsA : ∀ i ∈ s, AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (f i)) 0 :=
      fun i hi ↦ hA i (Finset.mem_insert_of_mem hi)
    have heq : (fun z ↦ ∏ i ∈ insert a s, f i z) = f a * (fun z ↦ ∏ i ∈ s, f i z) := by
      ext z
      simp [ha]
    rw [heq, UpperHalfPlane.qExpansion_mul (hA a (Finset.mem_insert_self _ _))
      (analytic_cusp_prod s f hsA), ih hsA, Finset.prod_insert ha]

private theorem coeff_one_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ)
    (h0 : ∀ i ∈ s, (f i).coeff 0 = 1) :
    (∏ i ∈ s, f i).coeff 1 = ∑ i ∈ s, (f i).coeff 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs0 : ∀ i ∈ s, (f i).coeff 0 = 1 := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
    have hc : PowerSeries.constantCoeff (∏ i ∈ s, f i) = 1 := by
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i hi
      simpa only [← PowerSeries.coeff_zero_eq_constantCoeff] using hs0 i hi
    rw [Finset.prod_insert ha, PowerSeries.coeff_one_mul, hc,
      ← PowerSeries.coeff_zero_eq_constantCoeff, h0 a (Finset.mem_insert_self _ _)]
    simp only [mul_one, ih hs0, Finset.sum_insert ha]

/-- The first coefficient of the Euler unit is minus the exponent of `η(z)`. -/
theorem qExpansion_unitPart_coeff_one (N : ℕ) (r : Fin N → ℤ) :
    (UpperHalfPlane.qExpansion 1 (unitPart N r)).coeff 1 = -(exponent r 1 : ℂ) := by
  change (UpperHalfPlane.qExpansion 1 (fun z ↦ ∏ m ∈ N.divisors,
    eulerFactorPower m (exponent r m) z)).coeff 1 = _
  rw [qExpansion_prod _ _ (fun m hm ↦ eulerFactorPower_analytic (Nat.pos_of_mem_divisors hm) _),
    coeff_one_prod _ _ (fun m hm ↦ eulerFactorPower_coeff_zero (Nat.pos_of_mem_divisors hm) _)]
  by_cases hN : N = 0
  · subst N
    simp [exponent]
  · rw [Finset.sum_eq_single_of_mem 1 (Nat.one_mem_divisors.mpr hN)]
    · simp only [qExpansion_eulerFactorPower_coeff_one (by norm_num : 0 < 1), ite_true]
    · intro m hm hm1
      rw [qExpansion_eulerFactorPower_coeff_one (Nat.pos_of_mem_divisors hm), ite_eq_right hm1]

/-- The coefficient immediately after the leading term is `-r₁`. -/
theorem qExpansion_coeff_leading_add_one {N : ℕ} {r : Fin N → ℤ} {v : ℕ}
    (hv : infinitySum N r = 24 * (v : ℤ)) :
    (UpperHalfPlane.qExpansion 1 (etaQuotient N r)).coeff (v + 1) = -(exponent r 1 : ℂ) := by
  rw [qExpansion_eq_X_pow_mul hv, add_comm v 1, PowerSeries.coeff_X_pow_mul,
    qExpansion_unitPart_coeff_one]

end WeightTwoCusps.EtaQuotient
