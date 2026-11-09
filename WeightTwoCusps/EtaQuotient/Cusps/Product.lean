module

public import WeightTwoCusps.EtaQuotient.Cusps.Bounds

/-!
# Factoring the slash of a product of eta squares

This identity is used in the general cusp analysis. It allows arbitrary
signed exponents; modular forms are constructed in `Constructor.lean`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex Filter OnePoint
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Topology

namespace WeightTwoCusps.EtaQuotient

private theorem prod_const_zpow {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (a : ℂ) (ha : a ≠ 0) : (∏ i ∈ s, a ^ f i) = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ ha]

/-- The slash of an eta quotient with doubled exponents factors into the
weight-one slashes of its eta-square factors, including negative powers. -/
theorem double_slash_eq_prod (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ)) :
    etaQuotient N (double r) ∣[exponentSum N r] γ =
      fun z : ℍ ↦ ∏ m ∈ N.divisors,
        (((fun w : ℍ ↦ ModularForm.eta ((m : ℂ) * (w : ℂ)) ^ 2) ∣[(1 : ℤ)] γ) z) ^
          exponent r m := by
  ext z
  simp only [ModularForm.SL_slash_apply, etaQuotient, exponent_double, zpow_mul,
    zpow_ofNat, Int.reduceNeg, zpow_neg_one, mul_zpow, Finset.prod_mul_distrib]
  rw [prod_const_zpow _ _ _ (inv_ne_zero (denom_ne_zero γ z))]
  congr 1
  rw [inv_zpow, exponentSum, zpow_neg]

end WeightTwoCusps.EtaQuotient
