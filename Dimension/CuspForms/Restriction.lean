module

public import Dimension.Periods.Basic
public import Mathlib.NumberTheory.ModularForms.NormTrace

@[expose] public section

/-!
# Restriction and dimension comparison for weight-two cusp forms

These statements apply to arbitrary finite-index subgroups of `SL₂(ℤ)`.
-/

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

/-- Restriction from a group to a subgroup, as a complex linear map. -/
def weightTwoCuspForms_restrict {Γ Δ : Subgroup SL(2, ℤ)} (h : Γ ≤ Δ) :
    CuspForm Δ 2 →ₗ[ℂ] CuspForm Γ 2 where
  toFun := CuspForm.restrict (Subgroup.map_mono h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem weightTwoCuspForms_restrict_apply {Γ Δ : Subgroup SL(2, ℤ)} (h : Γ ≤ Δ)
    (f : CuspForm Δ 2) (z : UpperHalfPlane) :
    weightTwoCuspForms_restrict h f z = f z := rfl

theorem weightTwoCuspForms_restrict_injective {Γ Δ : Subgroup SL(2, ℤ)} (h : Γ ≤ Δ) :
    Function.Injective (weightTwoCuspForms_restrict h) :=
  CuspForm.restrict_injective (Subgroup.map_mono h)

/-- Enlarging the congruence subgroup can only decrease the dimension. -/
theorem weightTwoCuspForms_finrank_le {Γ Δ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (h : Γ ≤ Δ) :
    Module.finrank ℂ (CuspForm Δ 2) ≤ Module.finrank ℂ (CuspForm Γ 2) :=
  LinearMap.finrank_le_finrank_of_injective (weightTwoCuspForms_restrict_injective h)

end WeightTwoCusps
