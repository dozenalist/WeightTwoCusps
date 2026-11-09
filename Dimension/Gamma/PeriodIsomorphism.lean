module

public import Dimension.Gamma.Formula
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# The real period isomorphism at principal level

The proved dimension relation upgrades the period injection to an isomorphism.
This is a possible starting point for descent to other congruence subgroups.
-/

noncomputable section

namespace WeightTwoCusps

open ModularCurve.Period

/-- The integral parabolic rank is twice the complex cusp-form dimension. -/
theorem principalParabolicHoms_finrank (N : ℕ) (hN : 2 ≤ N) :
    Module.finrank ℤ (parabolicHoms ℤ (CongruenceSubgroup.Gamma N) ℤ) =
      2 * Module.finrank ℂ (gammaCuspForms N) := by
  have hd := gammaCuspForms_dimension_relation N hN
  have hp := ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq N hN
  nlinarith

/-- The real periods are surjective at principal levels at least two. -/
theorem principal_realPeriods_bijective (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    Function.Bijective (realPeriods (CongruenceSubgroup.Gamma N)) := by
  letI : NeZero N := ⟨by omega⟩
  refine ⟨realPeriods_injective _, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (realPeriods_injective _)
  rw [finrank_real_of_complex, realParabolicHoms_finrank_eq_int, principalParabolicHoms_finrank N hN]

/-- Cusp forms, viewed as a real space, identify with real parabolic homomorphisms. -/
def principalRealPeriodEquiv (N : ℕ) (hN : 2 ≤ N) :
    gammaCuspForms N ≃ₗ[ℝ] parabolicHoms ℝ (CongruenceSubgroup.Gamma N) ℝ := by
  letI : NeZero N := ⟨by omega⟩
  exact LinearEquiv.ofBijective (realPeriods _) (principal_realPeriods_bijective N hN)

end WeightTwoCusps
