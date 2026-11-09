module

public import Dimension.Gamma_1.ProjectiveIndex
public import Dimension.Gamma_0.Arithmetic

@[expose] public section

/-!
# Arithmetic terms in the weight-two `Γ₁(N)` formula

For `N ≥ 5`, the cusp correction is one half of the totient convolution.
Level four is exceptional: it has three cusps, and the unmodified divisor-sum
expression would give `5/2`.
-/

namespace WeightTwoCusps

/-- The totient convolution; twice the classical cusp count for `N ≥ 5`. -/
def gamma1CuspSum (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors, Nat.totient d * Nat.totient (N / d)

/-- The classical cusp-count expression, including the exceptional small levels. -/
def gamma1CuspCount (N : ℕ) : ℚ :=
  if N ≤ 2 then gamma0CuspCount N
  else if N = 4 then 3
  else (gamma1CuspSum N : ℚ) / 2

/-- The arithmetic expression expected for the weight-two dimension.
The small positive levels have dimension zero; the nonexceptional expression
uses the projective index and the totient convolution. -/
noncomputable def gamma1Dimension (N : ℕ) : ℚ :=
  if N ≤ 4 then 0
  else 1 + (gamma1ProjectiveIndex N : ℚ) / 12 - (gamma1CuspSum N : ℚ) / 4

/-- The traditional prime-product expression for the arithmetic dimension. -/
theorem gamma1Dimension_eq_prime_product (N : ℕ) (hN : 5 ≤ N) :
    gamma1Dimension N =
      1 + (N : ℚ) ^ 2 / 24 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) -
        (gamma1CuspSum N : ℚ) / 4 := by
  rw [gamma1Dimension, if_neg (by omega), gamma1ProjectiveIndex_eq_prime_product N (by omega)]
  ring

/-- Solving the integral relation with the doubled cusp count. -/
lemma gamma1_dimension_rat_of_relation {d μ s : ℕ}
    (h : 12 * d + 3 * s = 12 + μ) :
    (d : ℚ) = 1 + (μ : ℚ) / 12 - (s : ℚ) / 4 := by
  have hq : (12 : ℚ) * d + 3 * s = 12 + μ := by exact_mod_cast h
  linarith

end WeightTwoCusps
