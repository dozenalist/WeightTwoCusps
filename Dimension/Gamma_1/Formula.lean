module

public import Dimension.Gamma_1.Arithmetic
public import Dimension.Gamma_1.Comparison
public import Dimension.Gamma_1.Relation
public import Dimension.Gamma_1.CuspModel

/-!
# Assembly of the `Γ₁(N)` prime-product dimension formula

The first-column cusp classification proves the totient divisor sum for `N ≥ 5`.
Together with the analytic comparison this gives the classical dimension formula.
The exceptional small positive levels are handled by restriction to principal level.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- An unconditional prime-product formula using the actual cusp orbit cardinal.
Replacing that cardinal by the classical divisor sum remains a separate step. -/
theorem gamma1CuspForms_dimension_formula_prime_product_geometric (N : ℕ) (hN : 4 ≤ N) :
    (Module.finrank ℂ (gamma1CuspForms N) : ℚ) =
      1 + (N : ℚ) ^ 2 / 24 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) -
        (gamma1GeometricCuspCount N : ℚ) / 2 := by
  have h := gamma1CuspForms_geometric_dimension_relation N hN
  have hq : (12 : ℚ) * Module.finrank ℂ (gamma1CuspForms N) +
      6 * gamma1GeometricCuspCount N = 12 + gamma1ProjectiveIndex N := by exact_mod_cast h
  have hd : (Module.finrank ℂ (gamma1CuspForms N) : ℚ) =
      1 + (gamma1ProjectiveIndex N : ℚ) / 12 - (gamma1GeometricCuspCount N : ℚ) / 2 := by
    linarith
  rw [hd, gamma1ProjectiveIndex_eq_prime_product N (by omega)]
  ring

/-- The classical divisor-sum formula needs only the remaining arithmetic cusp count. -/
theorem gamma1CuspForms_dimension_formula_prime_product_of_cusp_count
    (N : ℕ) (hN : 5 ≤ N)
    (hc : 2 * gamma1GeometricCuspCount N = gamma1CuspSum N) :
    (Module.finrank ℂ (gamma1CuspForms N) : ℚ) =
      1 + (N : ℚ) ^ 2 / 24 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) -
        (gamma1CuspSum N : ℚ) / 4 := by
  have hcQ : (2 : ℚ) * gamma1GeometricCuspCount N = gamma1CuspSum N := by exact_mod_cast hc
  rw [gamma1CuspForms_dimension_formula_prime_product_geometric N (by omega)]
  linarith

/-- The prime-product formula, conditional on the remaining dimension relation. -/
theorem gamma1CuspForms_dimension_formula_prime_product_of_relation (N : ℕ) (hN : 5 ≤ N)
    (h : 12 * Module.finrank ℂ (gamma1CuspForms N) + 3 * gamma1CuspSum N =
      12 + gamma1ProjectiveIndex N) :
    (Module.finrank ℂ (gamma1CuspForms N) : ℚ) =
      1 + (N : ℚ) ^ 2 / 24 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) -
        (gamma1CuspSum N : ℚ) / 4 := by
  rw [gamma1_dimension_rat_of_relation h, gamma1ProjectiveIndex_eq_prime_product N (by omega)]
  ring

theorem gamma1CuspForms_dimension_formula_of_relation (N : ℕ) (hN : 5 ≤ N)
    (h : 12 * Module.finrank ℂ (gamma1CuspForms N) + 3 * gamma1CuspSum N =
      12 + gamma1ProjectiveIndex N) :
    (Module.finrank ℂ (gamma1CuspForms N) : ℚ) = gamma1Dimension N := by
  rw [gamma1Dimension_eq_prime_product N hN]
  exact gamma1CuspForms_dimension_formula_prime_product_of_relation N hN h

/-- Twice the actual cusp count is the totient convolution outside the exceptional levels. -/
theorem gamma1GeometricCuspCount_eq_cuspSum (N : ℕ) (hN : 5 ≤ N) :
    2 * gamma1GeometricCuspCount N = gamma1CuspSum N :=
  two_mul_projectiveGamma1Cusps_card_eq_cuspSum N hN

/-- The unconditional classical prime-product dimension formula for `Γ₁(N)`. -/
theorem gamma1CuspForms_dimension_formula_prime_product (N : ℕ) (hN : 5 ≤ N) :
    (Module.finrank ℂ (gamma1CuspForms N) : ℚ) =
      1 + (N : ℚ) ^ 2 / 24 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) -
        (gamma1CuspSum N : ℚ) / 4 :=
  gamma1CuspForms_dimension_formula_prime_product_of_cusp_count N hN
    (gamma1GeometricCuspCount_eq_cuspSum N hN)

/-- The arithmetic dimension expression agrees with the genuine analytic space at every
positive level, including the exceptional levels one through four. -/
theorem gamma1CuspForms_dimension_formula (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (gamma1CuspForms N) : ℚ) = gamma1Dimension N := by
  by_cases hN : 5 ≤ N
  · rw [gamma1Dimension_eq_prime_product N hN]
    exact gamma1CuspForms_dimension_formula_prime_product N hN
  · rw [gamma1CuspForms_finrank_eq_zero_of_le_five N (by omega),
      gamma1Dimension, ite_eq_left (by omega)]
    rfl

end WeightTwoCusps
