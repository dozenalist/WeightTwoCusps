module

public import Dimension.GroupTheory.EllipticRank
public import Dimension.Gamma_0.EllipticOrbits

/-! # The dimension formula for weight-two cusp forms of level `Γ₀(N)` -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- The ordinary rational homomorphism rank, including both elliptic stabilizers. -/
theorem gamma0_hom_rank_relation (N : ℕ) [NeZero N] :
    6 * Module.finrank ℚ (Additive (CongruenceSubgroup.Gamma0 N) →+ ℚ) +
      3 * gamma0EllipticTwoCount N + 4 * gamma0EllipticThreeCount N =
        6 + (CongruenceSubgroup.Gamma0 N).index := by
  apply gamma0_hom_rank_relation_of_orbit_rank
  exact finrank_rationalHom_add_elliptic_orbits _ (neg_one_mem_Gamma0 N)

/-- The classical arithmetic dimension formula for the genuine analytic
weight-two cusp-form space, at every positive level. -/
theorem gamma0CuspForms_dimension_formula (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) = gamma0Dimension N := by
  by_cases hN : N = 1
  · subst N
    rw [gamma0CuspForms_finrank_eq_zero_of_le_five 1 (by decide)]
    have h₂ : gamma0EllipticTwoCount 1 = 1 := by decide
    have h₃ : gamma0EllipticThreeCount 1 = 1 := by decide
    have hc : gamma0CuspCount 1 = 1 := by decide
    norm_num [gamma0Dimension, CongruenceIndex.psi, h₂, h₃, hc]
  · have hNpos := NeZero.pos N
    exact gamma0CuspForms_dimension_formula_of_hom_rank N (by omega) (gamma0_hom_rank_relation N)

/-- The integral genus relation, with all cusp and elliptic counts identified arithmetically. -/
theorem gamma0CuspForms_dimension_relation (N : ℕ) [NeZero N] :
    12 * Module.finrank ℂ (gamma0CuspForms N) + 3 * gamma0EllipticTwoCount N +
      4 * gamma0EllipticThreeCount N + 6 * gamma0CuspCount N =
        12 + (CongruenceSubgroup.Gamma0 N).index := by
  have h := gamma0CuspForms_dimension_formula N
  rw [gamma0Dimension, ← CongruenceIndex.Gamma0_index'] at h
  have hq : (12 : ℚ) * Module.finrank ℂ (gamma0CuspForms N) + 3 * gamma0EllipticTwoCount N +
      4 * gamma0EllipticThreeCount N + 6 * gamma0CuspCount N =
        12 + (CongruenceSubgroup.Gamma0 N).index := by linarith
  exact_mod_cast hq

/-- The explicit prime-product, elliptic-root-count, and cusp-divisor-sum formula. -/
theorem gamma0CuspForms_dimension_formula_prime_product (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) =
      1 + (N : ℚ) / 12 * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) -
        (gamma0EllipticTwoCount N : ℚ) / 4 -
        (gamma0EllipticThreeCount N : ℚ) / 3 - (gamma0CuspCount N : ℚ) / 2 := by
  rw [gamma0CuspForms_dimension_formula, gamma0Dimension, CongruenceIndex.psi]
  ring

end WeightTwoCusps
