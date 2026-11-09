module

public import WeightTwoCusps.EtaQuotient.QExpansion.LowCoefficients

/-! # Structural properties of eta-quotient coefficients -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open UpperHalfPlane

namespace WeightTwoCusps.EtaQuotient

@[simp] theorem unitCoefficient_zero (N : ℕ) (r : Fin N → ℤ) :
    unitCoefficient N r 0 = 1 := by
  have h := qExpansion_unitPart_coeff N r 0
  rw [qExpansion_unitPart_coeff_zero] at h
  exact_mod_cast h.symm

@[simp] theorem unitCoefficient_one (N : ℕ) (r : Fin N → ℤ) :
    unitCoefficient N r 1 = -exponent r 1 := by
  have h := qExpansion_unitPart_coeff N r 1
  rw [qExpansion_unitPart_coeff_one] at h
  exact_mod_cast h.symm

/-- An integer form of the second-coefficient formula, with denominators cleared. -/
theorem two_mul_unitCoefficient_two (N : ℕ) (r : Fin N → ℤ) :
    2 * unitCoefficient N r 2 =
      exponent r 1 * (exponent r 1 - 3) - 2 * divisorExponent N r 2 := by
  have h := qExpansion_unitPart_coeff_two N r
  rw [qExpansion_unitPart_coeff] at h
  have h' : (2 : ℂ) * (unitCoefficient N r 2 : ℂ) =
      (exponent r 1 : ℂ) * ((exponent r 1 : ℂ) - 3) -
        2 * (divisorExponent N r 2 : ℂ) := by
    linear_combination 2 * h
  exact_mod_cast h'

theorem unitCoefficient_two (N : ℕ) (r : Fin N → ℤ) :
    unitCoefficient N r 2 =
      exponent r 1 * (exponent r 1 - 3) / 2 - divisorExponent N r 2 := by
  have h := two_mul_unitCoefficient_two N r
  omega

/-- Integer coefficients give real analytic coefficients, even for signed exponents. -/
theorem qExpansion_coeff_im {N : ℕ} {r : Fin N → ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) (h0 : 0 ≤ infinitySum N r) (n : ℕ) :
    ((qExpansion 1 (etaQuotient N r)).coeff n).im = 0 := by
  rw [qExpansion_coeff_eq_coefficient hi h0]
  simp

theorem qExpansion_coeff_re {N : ℕ} {r : Fin N → ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) (h0 : 0 ≤ infinitySum N r) (n : ℕ) :
    ((qExpansion 1 (etaQuotient N r)).coeff n).re = (coefficient N r n : ℝ) := by
  rw [qExpansion_coeff_eq_coefficient hi h0]
  simp

/-- The whole analytic expansion is the series built from the integer algorithm. -/
theorem qExpansion_eq_mk_coefficient {N : ℕ} {r : Fin N → ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) (h0 : 0 ≤ infinitySum N r) :
    qExpansion 1 (etaQuotient N r) = PowerSeries.mk (fun n ↦ (coefficient N r n : ℂ)) := by
  ext n
  simpa using qExpansion_coeff_eq_coefficient hi h0 n

/-- The computable integer coefficients give a convergent series everywhere on `ℍ`. -/
theorem hasSum_coefficient {N : ℕ} {r : Fin N → ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) (h0 : 0 ≤ infinitySum N r) (z : ℍ) :
    HasSum (fun n ↦ (coefficient N r n : ℂ) * Function.Periodic.qParam 1 z ^ n)
      (etaQuotient N r z) := by
  have hs := hasSum_etaQuotient (infinitySum_eq_twentyFour_mul_order hi h0) z
  rw [← qExpansion_eq_X_pow_mul (infinitySum_eq_twentyFour_mul_order hi h0)] at hs
  simpa only [qExpansion_coeff_eq_coefficient hi h0] using hs

/-- An eta quotient with nonnegative integral infinity order has a nonzero expansion. -/
theorem qExpansion_ne_zero {N : ℕ} {r : Fin N → ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) (h0 : 0 ≤ infinitySum N r) :
    qExpansion 1 (etaQuotient N r) ≠ 0 := by
  intro hz
  have h := qExpansion_coeff_leading (infinitySum_eq_twentyFour_mul_order hi h0)
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- The arithmetic hypotheses alone give analyticity at the q-disc origin. -/
theorem etaQuotient_analyticAt_cuspFunction {N : ℕ} {r : Fin N → ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) (h0 : 0 ≤ infinitySum N r) :
    AnalyticAt ℂ (cuspFunction 1 (etaQuotient N r)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num)
    (periodic_of_infinity_congruence hi) (holo N r) (isBoundedAtImInfty_of_nonneg h0)

/-- Adding divisor exponents multiplies the full analytic q-expansions. -/
theorem qExpansion_mul_of_exponent_add {N : ℕ} {r s t : Fin N → ℤ}
    (h : ∀ m ∈ N.divisors, exponent t m = exponent r m + exponent s m)
    (hri : (24 : ℤ) ∣ infinitySum N r) (hr0 : 0 ≤ infinitySum N r)
    (hsi : (24 : ℤ) ∣ infinitySum N s) (hs0 : 0 ≤ infinitySum N s) :
    qExpansion 1 (etaQuotient N t) =
      qExpansion 1 (etaQuotient N r) * qExpansion 1 (etaQuotient N s) := by
  have heq : etaQuotient N t = etaQuotient N r * etaQuotient N s :=
    funext (mul_of_exponent_add N r s t h)
  rw [heq]
  exact UpperHalfPlane.qExpansion_mul (etaQuotient_analyticAt_cuspFunction hri hr0)
    (etaQuotient_analyticAt_cuspFunction hsi hs0)

/-- The resulting coefficient is the finite Cauchy product. -/
theorem qExpansion_coeff_mul_of_exponent_add {N : ℕ} {r s t : Fin N → ℤ}
    (h : ∀ m ∈ N.divisors, exponent t m = exponent r m + exponent s m)
    (hri : (24 : ℤ) ∣ infinitySum N r) (hr0 : 0 ≤ infinitySum N r)
    (hsi : (24 : ℤ) ∣ infinitySum N s) (hs0 : 0 ≤ infinitySum N s) (n : ℕ) :
    (qExpansion 1 (etaQuotient N t)).coeff n =
      (convolution (coefficient N r) (coefficient N s) n : ℂ) := by
  rw [qExpansion_mul_of_exponent_add h hri hr0 hsi hs0]
  exact convolution_cast (qExpansion_coeff_eq_coefficient hri hr0)
    (qExpansion_coeff_eq_coefficient hsi hs0) n

end WeightTwoCusps.EtaQuotient
