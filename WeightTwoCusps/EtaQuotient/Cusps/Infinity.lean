module

public import WeightTwoCusps.EtaQuotient.Transformation.Translation
public import WeightTwoCusps.EtaQuotient.Criteria

/-!
# The leading term of an eta quotient at infinity

The remaining Euler-product factor tends to one, including for negative
exponents. Thus positive leading order implies vanishing at infinity, and
nonnegative leading order implies boundedness there.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Function Complex Filter
open UpperHalfPlane hiding I
open scoped Topology Manifold ModularForm Real MatrixGroups

namespace WeightTwoCusps.EtaQuotient

/-- The Euler product part of eta, without its exponential prefactor. -/
def eulerPart (z : ℂ) : ℂ := ∏' n : ℕ, (1 - ModularForm.eta_q n z)

/-- The product of the Euler factors in an eta quotient. -/
def unitPart (N : ℕ) (r : Fin N → ℤ) (z : ℍ) : ℂ :=
  ∏ m ∈ N.divisors, eulerPart ((m : ℂ) * (z : ℂ)) ^ exponent r m

theorem unitPart_ne_zero (N : ℕ) (r : Fin N → ℤ) (z : ℍ) : unitPart N r z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro m hm
  apply zpow_ne_zero
  apply ModularForm.eta_tprod_ne_zero
  simpa using mul_pos (show (0 : ℝ) < m by exact_mod_cast Nat.pos_of_mem_divisors hm) z.im_pos

/-- The exact leading exponential, before imposing either Newman congruence. -/
theorem eq_exp_mul_unitPart (N : ℕ) (r : Fin N → ℤ) (z : ℍ) :
    etaQuotient N r z =
      Complex.exp (2 * π * I * (z : ℂ) * (infinitySum N r : ℂ) / 24) * unitPart N r z := by
  simp only [etaQuotient, ModularForm.eta, Periodic.qParam, Complex.ofReal_ofNat,
    mul_zpow, Finset.prod_mul_distrib, unitPart, eulerPart]
  congr 1
  simp_rw [← Complex.exp_int_mul]
  rw [← Complex.exp_sum]
  congr 1
  rw [infinitySum, Int.cast_sum, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  push_cast
  ring

theorem eulerPart_dilate_tendsto_one {m : ℕ} (hm : 0 < m) :
    Tendsto (fun z : ℍ ↦ eulerPart ((m : ℂ) * (z : ℂ))) atImInfty (𝓝 1) := by
  have hprod : Tendsto (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
    have h := ModularForm.differentiableOn_tprod_one_sub_pow.differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (show (0 : ℝ) < 1 by norm_num)))
    simpa using h.continuousAt.tendsto
  have hq := (qParam_tendsto_atImInfty (show (0 : ℝ) < 1 by norm_num)).comp
    (Eta.tendsto_dilate_atImInfty m (by exact_mod_cast hm))
  simpa [eulerPart, ModularForm.eta_q, Function.comp_def, Eta.dilate] using hprod.comp hq

/-- The normalized Euler-product factor tends to one for every integer exponent function. -/
theorem unitPart_tendsto_one (N : ℕ) (r : Fin N → ℤ) :
    Tendsto (unitPart N r) atImInfty (𝓝 1) := by
  have h := tendsto_finsetProd N.divisors (fun m hm ↦
    (eulerPart_dilate_tendsto_one (Nat.pos_of_mem_divisors hm)).zpow₀
      (exponent r m) (Or.inl (by simp : (1 : ℂ) ≠ 0)))
  change Tendsto (fun z : ℍ ↦ ∏ m ∈ N.divisors,
    eulerPart ((m : ℂ) * (z : ℂ)) ^ exponent r m) atImInfty (𝓝 1)
  convert h using 1
  simp

/-- For a positive weighted exponent sum the quotient tends to zero. -/
theorem isZeroAtImInfty_of_pos {N : ℕ} {r : Fin N → ℤ} (h : 0 < infinitySum N r) :
    IsZeroAtImInfty (etaQuotient N r) := by
  have hperiod : (0 : ℝ) < 24 / (infinitySum N r : ℝ) := by positivity
  have hq := qParam_tendsto_atImInfty hperiod
  have heq : (fun z : ℍ ↦ Complex.exp
      (2 * π * I * (z : ℂ) * (infinitySum N r : ℂ) / 24)) =
      (fun z : ℍ ↦ Periodic.qParam (24 / (infinitySum N r : ℝ)) z) := by
    funext z
    simp only [Periodic.qParam, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_intCast]
    congr 1
    field_simp
  change Tendsto _ atImInfty (𝓝 0)
  have hp : Tendsto (fun z : ℍ ↦ Complex.exp
      (2 * π * I * (z : ℂ) * (infinitySum N r : ℂ) / 24) * unitPart N r z)
      atImInfty (𝓝 0) := by
    have hp' := (heq.symm ▸ hq).mul (unitPart_tendsto_one N r)
    rw [zero_mul] at hp'
    exact hp'
  exact hp.congr (fun z ↦ (eq_exp_mul_unitPart N r z).symm)

theorem tendsto_one_of_infinitySum_eq_zero {N : ℕ} {r : Fin N → ℤ}
    (h : infinitySum N r = 0) : Tendsto (etaQuotient N r) atImInfty (𝓝 1) := by
  have heq : etaQuotient N r = unitPart N r := by
    funext z
    simp [eq_exp_mul_unitPart, h]
  rw [heq]
  exact unitPart_tendsto_one N r

/-- Nonnegative leading order suffices for boundedness at infinity. -/
theorem isBoundedAtImInfty_of_nonneg {N : ℕ} {r : Fin N → ℤ} (h : 0 ≤ infinitySum N r) :
    IsBoundedAtImInfty (etaQuotient N r) := by
  rcases h.eq_or_lt with heq | hpos
  · exact (tendsto_one_of_infinitySum_eq_zero heq.symm).isBigO_one ℝ
  · exact (isZeroAtImInfty_of_pos hpos).boundedAtFilter

/-- The magnitude of the leading exponential has the expected real exponent. -/
theorem norm_eq_exp_mul_unitPart (N : ℕ) (r : Fin N → ℤ) (z : ℍ) :
    ‖etaQuotient N r z‖ =
      Real.exp ((-2 * π * (infinitySum N r : ℝ) / 24) * z.im) * ‖unitPart N r z‖ := by
  rw [eq_exp_mul_unitPart, norm_mul, Complex.norm_exp]
  congr 2
  simp only [div_ofNat_re, mul_re, mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Complex.intCast_re,
    Complex.intCast_im, zero_mul, mul_zero, add_zero, zero_add, mul_one, sub_zero,
    zero_sub, UpperHalfPlane.coe_im]
  ring

/-- Negative leading order makes the absolute value diverge at infinity. -/
theorem norm_tendsto_atTop_of_neg {N : ℕ} {r : Fin N → ℤ} (h : infinitySum N r < 0) :
    Tendsto (fun z : ℍ ↦ ‖etaQuotient N r z‖) atImInfty atTop := by
  have hc : 0 < -2 * π * (infinitySum N r : ℝ) / 24 := by
    have hr : (infinitySum N r : ℝ) < 0 := by exact_mod_cast h
    rw [show -2 * π * (infinitySum N r : ℝ) / 24 =
      (2 * π * -(infinitySum N r : ℝ)) / 24 by ring]
    exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
      (neg_pos.mpr hr)) (by norm_num)
  have hi : Tendsto (fun z : ℍ ↦ z.im) atImInfty atTop := Filter.tendsto_comap
  have he := Real.tendsto_exp_atTop.comp (hi.const_mul_atTop hc)
  have hu : Tendsto (fun z : ℍ ↦ ‖unitPart N r z‖) atImInfty (𝓝 1) := by
    simpa using (unitPart_tendsto_one N r).norm
  exact (he.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hu).congr
    (fun z ↦ (norm_eq_exp_mul_unitPart N r z).symm)

/-- The infinity part of Ligozat's criterion, in both directions. -/
theorem isBoundedAtImInfty_iff (N : ℕ) (r : Fin N → ℤ) :
    IsBoundedAtImInfty (etaQuotient N r) ↔ 0 ≤ infinitySum N r := by
  refine ⟨fun h ↦ ?_, isBoundedAtImInfty_of_nonneg⟩
  by_contra hn
  have ht := norm_tendsto_atTop_of_neg (lt_of_not_ge hn)
  exact Filter.not_isBoundedUnder_of_tendsto_atTop ht
    ((Asymptotics.isBigO_one_iff ℝ).mp h)

theorem isZeroAtImInfty_iff (N : ℕ) (r : Fin N → ℤ) :
    IsZeroAtImInfty (etaQuotient N r) ↔ 0 < infinitySum N r := by
  refine ⟨fun h ↦ ?_, isZeroAtImInfty_of_pos⟩
  have hn := (isBoundedAtImInfty_iff N r).mp h.boundedAtFilter
  rcases hn.eq_or_lt with heq | hpos
  · have hlim := tendsto_one_of_infinitySum_eq_zero heq.symm
    have he := tendsto_nhds_unique h hlim
    exact False.elim (zero_ne_one he)
  · exact hpos

end WeightTwoCusps.EtaQuotient

