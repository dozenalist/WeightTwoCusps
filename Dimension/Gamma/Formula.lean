module

public import Dimension.Gamma.Arithmetic
public import Dimension.Gamma.Relation
public import Dimension.Gamma.ProjectiveIndex

@[expose] public section

/-!
# Dimension of weight-two cusp forms for `Γ(N)`

The period argument and the Riemann–Roch lower bound give the integral
relation in `gammaCuspForms_dimension_relation`. The results below solve
that relation, including the level-one exception.
-/

noncomputable section

namespace WeightTwoCusps

/-- The dimension formula for positive principal level, as a natural number. -/
theorem gammaCuspForms_dimension_formula (N : ℕ) [NeZero N] :
    Module.finrank ℂ (gammaCuspForms N) = gammaDimension N := by
  by_cases hN : N = 1
  · subst N
    simp [gammaDimension, gammaCuspForms_finrank_one]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hNtwo : 2 ≤ N := by omega
    simp only [gammaDimension, if_neg hN]
    exact dimension_nat_of_relation hNpos (gammaCuspForms_dimension_relation N hNtwo)

/-- For `N ≥ 2`, the classical formula
`dim S₂(Γ(N)) = 1 + μ (N - 6) / (12 N)`, where `μ` is the projective index.
The rational expression also handles the genus-zero levels below six. -/
theorem gammaCuspForms_dimension_formula_rat (N : ℕ) (hN : 2 ≤ N) :
    (Module.finrank ℂ (gammaCuspForms N) : ℚ) =
      1 + (projectiveIndex N : ℚ) * ((N : ℚ) - 6) / (12 * N) :=
  dimension_rat_of_relation (by omega) (gammaCuspForms_dimension_relation N hN)

/-- At principal level six the space is one-dimensional. -/
theorem gammaCuspForms_finrank_six : Module.finrank ℂ (gammaCuspForms 6) = 1 := by
  have h := gammaCuspForms_dimension_formula_rat 6 (by decide)
  norm_num at h
  exact_mod_cast h

/-- The traditional dimension formula for principal level `N ≥ 3`, with the
product taken over the prime divisors of `N`. All subtraction is in `ℚ`. -/
theorem gammaCuspForms_dimension_formula_prime_product (N : ℕ) (hN : 3 ≤ N) :
    (Module.finrank ℂ (gammaCuspForms N) : ℚ) =
      1 + (N : ℚ) ^ 2 * ((N : ℚ) - 6) / 24 *
        ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  rw [gammaCuspForms_dimension_formula_rat N (by omega),
    projectiveIndex_eq_prime_product N hN]
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp [hNq]
  ring

/-- The principal level-two space vanishes. -/
theorem gammaCuspForms_finrank_two : Module.finrank ℂ (gammaCuspForms 2) = 0 := by
  have h := gammaCuspForms_dimension_formula_rat 2 (by decide)
  norm_num [projectiveIndex_two] at h
  exact_mod_cast h

theorem gammaCuspForms_finrank_three : Module.finrank ℂ (gammaCuspForms 3) = 0 := by
  have h := gammaCuspForms_dimension_formula_prime_product 3 (by decide)
  norm_num [Nat.prime_three.primeFactors] at h
  exact_mod_cast h

theorem gammaCuspForms_finrank_four : Module.finrank ℂ (gammaCuspForms 4) = 0 := by
  have h := gammaCuspForms_dimension_formula_prime_product 4 (by decide)
  have hfac : (4 : ℕ).primeFactors = {2} := by
    simpa using Nat.primeFactors_prime_pow (show 2 ≠ 0 by decide) Nat.prime_two
  norm_num [hfac] at h
  exact_mod_cast h

theorem gammaCuspForms_finrank_five : Module.finrank ℂ (gammaCuspForms 5) = 0 := by
  have h := gammaCuspForms_dimension_formula_prime_product 5 (by decide)
  norm_num [(show Nat.Prime 5 by decide).primeFactors] at h
  exact_mod_cast h

/-- All positive principal levels at most five have genus zero. -/
theorem gammaCuspForms_finrank_eq_zero_of_le_five (N : ℕ) [NeZero N] (hN : N ≤ 5) :
    Module.finrank ℂ (gammaCuspForms N) = 0 := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  interval_cases N
  · exact gammaCuspForms_finrank_one
  · exact gammaCuspForms_finrank_two
  · exact gammaCuspForms_finrank_three
  · exact gammaCuspForms_finrank_four
  · exact gammaCuspForms_finrank_five

end WeightTwoCusps
