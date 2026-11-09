module

public import Dimension.Gamma_0.Arithmetic
public import Dimension.Gamma_0.Comparison
public import Dimension.Gamma_0.Relation
public import Dimension.Gamma_0.CuspCount

@[expose] public section

/-!
# Assembly of the `Γ₀(N)` prime-product dimension formula

The divisor-sum cusp count gives the classical arithmetic formula whenever
the two elliptic root obstructions are absent. The general formula with
elliptic corrections still has an explicit homomorphism-rank hypothesis.
-/

noncomputable section

namespace WeightTwoCusps

/-- An unconditional prime-product formula for `4 ∣ N`, with the actual cusp count. -/
theorem gamma0CuspForms_dimension_formula_prime_product_geometric_of_four_dvd
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) =
      1 + (N : ℚ) / 12 * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) -
        (gamma0GeometricCuspCount N : ℚ) / 2 := by
  have h := gamma0CuspForms_geometric_dimension_relation_of_four_dvd N hN
  have hq : (12 : ℚ) * Module.finrank ℂ (gamma0CuspForms N) +
      6 * gamma0GeometricCuspCount N = 12 + (CongruenceSubgroup.Gamma0 N).index := by
    exact_mod_cast h
  have hd : (Module.finrank ℂ (gamma0CuspForms N) : ℚ) =
      1 + ((CongruenceSubgroup.Gamma0 N).index : ℚ) / 12 -
        (gamma0GeometricCuspCount N : ℚ) / 2 := by linarith
  rw [hd, CongruenceIndex.Gamma0_index', CongruenceIndex.psi]
  ring

/-- The desired formula follows from the integral dimension relation.
The hypothesis records the remaining analytic/geometric input explicitly. -/
theorem gamma0CuspForms_dimension_formula_prime_product_of_relation (N : ℕ) [NeZero N]
    (h : 12 * Module.finrank ℂ (gamma0CuspForms N) + 3 * gamma0EllipticTwoCount N +
      4 * gamma0EllipticThreeCount N + 6 * gamma0CuspCount N =
        12 + (CongruenceSubgroup.Gamma0 N).index) :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) =
      1 + (N : ℚ) / 12 * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) -
        (gamma0EllipticTwoCount N : ℚ) / 4 -
        (gamma0EllipticThreeCount N : ℚ) / 3 - (gamma0CuspCount N : ℚ) / 2 := by
  rw [gamma0_dimension_rat_of_relation h, CongruenceIndex.Gamma0_index', CongruenceIndex.psi]
  ring

theorem gamma0CuspForms_dimension_formula_of_relation (N : ℕ) [NeZero N]
    (h : 12 * Module.finrank ℂ (gamma0CuspForms N) + 3 * gamma0EllipticTwoCount N +
      4 * gamma0EllipticThreeCount N + 6 * gamma0CuspCount N =
        12 + (CongruenceSubgroup.Gamma0 N).index) :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) = gamma0Dimension N := by
  rw [gamma0Dimension, ← CongruenceIndex.Gamma0_index']
  exact gamma0_dimension_rat_of_relation h

/-- The classical divisor-sum formula for every positive multiple of four. -/
theorem gamma0CuspForms_dimension_formula_prime_product_of_four_dvd
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) =
      1 + (N : ℚ) / 12 * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) -
        (gamma0CuspCount N : ℚ) / 2 := by
  simpa only [gamma0GeometricCuspCount_eq_cuspCount] using
    gamma0CuspForms_dimension_formula_prime_product_geometric_of_four_dvd N hN

/-- The full arithmetic dimension formula whenever both elliptic polynomials
have no roots, at arbitrary composite as well as prime levels. -/
theorem gamma0CuspForms_dimension_formula_of_no_roots (N : ℕ) (hN : 2 ≤ N)
    (h₂ : ∀ a : ZMod N, a ^ 2 + 1 ≠ 0)
    (h₃ : ∀ a : ZMod N, a ^ 2 + a + 1 ≠ 0) :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) = gamma0Dimension N := by
  letI : NeZero N := ⟨by omega⟩
  apply gamma0CuspForms_dimension_formula_of_relation
  have h := gamma0CuspForms_geometric_dimension_relation_of_trace_ne N hN
    (Gamma0_trace_ne_of_no_roots N h₂ h₃)
  simpa only [gamma0EllipticTwoCount_eq_zero_of_no_roots N h₂,
    gamma0EllipticThreeCount_eq_zero_of_no_roots N h₃, mul_zero, add_zero,
    gamma0GeometricCuspCount_eq_cuspCount] using h

/-- Positive multiples of four have the classical arithmetic dimension. -/
theorem gamma0CuspForms_dimension_formula_of_four_dvd (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) = gamma0Dimension N := by
  have hNfour : 4 ≤ N := Nat.le_of_dvd (NeZero.pos N) hN
  apply gamma0CuspForms_dimension_formula_of_no_roots N (by omega)
  · intro a ha
    have h := congrArg (ZMod.castHom hN (ZMod 4)) ha
    simp only [map_add, map_pow, map_one, map_zero] at h
    exact (by decide : ∀ x : ZMod 4, x ^ 2 + 1 ≠ 0) _ h
  · intro a ha
    have h := congrArg (ZMod.castHom hN (ZMod 4)) ha
    simp only [map_add, map_pow, map_one, map_zero] at h
    exact (by decide : ∀ x : ZMod 4, x ^ 2 + x + 1 ≠ 0) _ h

/-- The only remaining general input is the ordinary rational homomorphism rank,
including the contributions of the finite elliptic stabilizers. -/
theorem gamma0CuspForms_dimension_formula_of_hom_rank (N : ℕ) (hN : 2 ≤ N)
    (hrank : 6 * Module.finrank ℚ (Additive (CongruenceSubgroup.Gamma0 N) →+ ℚ) +
      3 * gamma0EllipticTwoCount N + 4 * gamma0EllipticThreeCount N =
        6 + (CongruenceSubgroup.Gamma0 N).index) :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) = gamma0Dimension N := by
  letI : NeZero N := ⟨by omega⟩
  have hgeom := gamma0CuspForms_geometric_dimension_relation N hN
  rw [gamma0GeometricCuspCount_eq_cuspCount] at hgeom
  apply gamma0CuspForms_dimension_formula_of_relation
  omega

end WeightTwoCusps
