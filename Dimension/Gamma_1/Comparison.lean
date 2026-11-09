module

public import Dimension.Gamma_1.Basic
public import Dimension.Gamma_1.Index
public import Dimension.Gamma.Formula

@[expose] public section

/-! # Dimension bounds and genus-zero levels for `Γ₁(N)` -/

noncomputable section

namespace WeightTwoCusps

/-- Restriction to principal level gives an upper bound. -/
theorem gamma1CuspForms_finrank_le_principal (N : ℕ) [NeZero N] :
    Module.finrank ℂ (gamma1CuspForms N) ≤ Module.finrank ℂ (gammaCuspForms N) :=
  weightTwoCuspForms_finrank_le (CongruenceIndex.Gamma_le_Gamma1 N)

/-- A prime-product upper bound from the principal-level result. -/
theorem gamma1CuspForms_finrank_le_prime_product (N : ℕ) (hN : 3 ≤ N) :
    (Module.finrank ℂ (gamma1CuspForms N) : ℚ) ≤
      1 + (N : ℚ) ^ 2 * ((N : ℚ) - 6) / 24 *
        ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  letI : NeZero N := ⟨by omega⟩
  rw [← gammaCuspForms_dimension_formula_prime_product N hN]
  exact_mod_cast gamma1CuspForms_finrank_le_principal N

/-- The analytic weight-two `Γ₁(N)` space is zero for positive `N ≤ 5`. -/
theorem gamma1CuspForms_finrank_eq_zero_of_le_five (N : ℕ) [NeZero N] (hN : N ≤ 5) :
    Module.finrank ℂ (gamma1CuspForms N) = 0 := by
  have h := gamma1CuspForms_finrank_le_principal N
  rw [gammaCuspForms_finrank_eq_zero_of_le_five N hN] at h
  omega

theorem gamma1CuspForms_eq_zero_of_le_five (N : ℕ) [NeZero N] (hN : N ≤ 5)
    (f : gamma1CuspForms N) : f = 0 :=
  finrank_zero_iff_forall_zero.mp (gamma1CuspForms_finrank_eq_zero_of_le_five N hN) f

end WeightTwoCusps
