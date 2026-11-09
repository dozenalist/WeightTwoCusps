module

import WeightTwoCusps.EtaQuotient.QExpansion

/-! # Checks of the public coefficient API with ordinary imports -/

open WeightTwoCusps WeightTwoCusps.EtaQuotient UpperHalfPlane

-- The computational definitions reduce without importing private Mathlib bodies.
example : eulerCoefficient 0 = 1 := by decide +kernel
example : eulerCoefficient 1 = -1 := by decide +kernel
example : eulerCoefficient 2 = -1 := by decide +kernel
example : eulerCoefficient 5 = 1 := by decide +kernel
example : divisorList 0 = [] := by decide +kernel
example : divisorList 12 = [1, 2, 3, 4, 6, 12] := by decide +kernel

-- Symbolic low coefficients, including irrelevant exponent entries.
example {N : ℕ} (r : Fin N → ℤ) : unitCoefficient N r 0 = 1 := by simp
example {N : ℕ} (r : Fin N → ℤ) : unitCoefficient N r 1 = -exponent r 1 := by simp

example : (qExpansion 1 (etaQuotient 1 ![24])).coeff 3 = 252 := by
  rw [qExpansion_coeff_leading_add_two (v := 1) (by decide +kernel)]
  norm_num [exponent, divisorExponent]

example : (qExpansion 1 (etaQuotient 3 ![24, 999, 0])).coeff 3 = 252 := by
  rw [qExpansion_coeff_leading_add_two (v := 1) (by decide +kernel)]
  norm_num [exponent, divisorExponent]

example : ((qExpansion 1 (etaQuotient 1 ![24])).coeff 7).im = 0 :=
  qExpansion_coeff_im (by decide +kernel) (by decide +kernel) 7

-- Nonnegative integral infinity order alone is sufficient; no modularity proof is used.
example (N : ℕ) (r : Fin N → ℤ) (hi : (24 : ℤ) ∣ infinitySum N r)
    (h0 : 0 ≤ infinitySum N r) (n : ℕ) :
    ∃ a : ℤ, (qExpansion 1 (etaQuotient N r)).coeff n = (a : ℂ) :=
  qExpansion_coeff_integral hi h0 n
