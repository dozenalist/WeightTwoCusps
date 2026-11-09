module

public import Dimension.Gamma_0.Basic
public import Dimension.Gamma.Formula

@[expose] public section

/-! # Dimension bounds and genus-zero levels for `Γ₀(N)` -/

noncomputable section

namespace WeightTwoCusps

/-- Restriction to principal level gives an upper bound. -/
theorem gamma0CuspForms_finrank_le_principal (N : ℕ) [NeZero N] :
    Module.finrank ℂ (gamma0CuspForms N) ≤ Module.finrank ℂ (gammaCuspForms N) := by
  apply weightTwoCuspForms_finrank_le
  intro γ hγ
  exact CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hγ).2.2.1

/-- A prime-product upper bound, available without elliptic-point or cusp counts. -/
theorem gamma0CuspForms_finrank_le_prime_product (N : ℕ) (hN : 3 ≤ N) :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) ≤
      1 + (N : ℚ) ^ 2 * ((N : ℚ) - 6) / 24 *
        ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  letI : NeZero N := ⟨by omega⟩
  rw [← gammaCuspForms_dimension_formula_prime_product N hN]
  exact_mod_cast gamma0CuspForms_finrank_le_principal N

/-- The analytic weight-two `Γ₀(N)` space is zero for positive `N ≤ 5`. -/
theorem gamma0CuspForms_finrank_eq_zero_of_le_five (N : ℕ) [NeZero N] (hN : N ≤ 5) :
    Module.finrank ℂ (gamma0CuspForms N) = 0 := by
  have h := gamma0CuspForms_finrank_le_principal N
  rw [gammaCuspForms_finrank_eq_zero_of_le_five N hN] at h
  omega

theorem gamma0CuspForms_eq_zero_of_le_five (N : ℕ) [NeZero N] (hN : N ≤ 5)
    (f : gamma0CuspForms N) : f = 0 :=
  finrank_zero_iff_forall_zero.mp (gamma0CuspForms_finrank_eq_zero_of_le_five N hN) f

end WeightTwoCusps
