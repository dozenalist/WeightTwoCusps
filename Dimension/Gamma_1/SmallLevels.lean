module

public import Dimension.Gamma_1.Formula

/-! # Actual cusp counts at the boundary of the `Γ₁(N)` formula -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- Level four really has three cusp orbits, including its irregular cusp. -/
theorem gamma1GeometricCuspCount_four : gamma1GeometricCuspCount 4 = 3 := by
  have hfac : (4 : ℕ).primeFactors = {2} := by
    simpa using Nat.primeFactors_prime_pow (show 2 ≠ 0 by decide) Nat.prime_two
  have hi := gamma1ProjectiveIndex_eq_prime_product 4 (by decide)
  norm_num [hfac] at hi
  have hiNat : gamma1ProjectiveIndex 4 = 6 := by exact_mod_cast hi
  have hr := gamma1CuspForms_geometric_dimension_relation 4 (by decide)
  rw [gamma1CuspForms_finrank_eq_zero_of_le_five 4 (by decide), hiNat] at hr
  omega

/-- At level five, the actual cusp orbit count agrees with the classical value four. -/
theorem gamma1GeometricCuspCount_five : gamma1GeometricCuspCount 5 = 4 := by
  have hi := gamma1ProjectiveIndex_eq_prime_product 5 (by decide)
  norm_num [(show Nat.Prime 5 by decide).primeFactors] at hi
  have hiNat : gamma1ProjectiveIndex 5 = 12 := by exact_mod_cast hi
  have hr := gamma1CuspForms_geometric_dimension_relation 5 (by decide)
  rw [gamma1CuspForms_finrank_eq_zero_of_le_five 5 (by decide), hiNat] at hr
  omega

/-- The unmodified divisor sum at level four is five, hence does not equal twice
the actual cusp count. This is why the divisor-sum formula excludes that level. -/
theorem gamma1CuspSum_four : gamma1CuspSum 4 = 5 := by decide

/-- The divisor-sum cusp identity holds at the first nonexceptional level. -/
theorem gamma1CuspSum_five_eq_twice_geometric :
    gamma1CuspSum 5 = 2 * gamma1GeometricCuspCount 5 := by
  rw [gamma1GeometricCuspCount_five]
  decide

end WeightTwoCusps
