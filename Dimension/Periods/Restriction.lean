module

public import Dimension.CuspForms.Restriction

@[expose] public section

/-! # Restriction of real periods to a finite-index subgroup -/

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

open ModularCurve ModularCurve.Period

/-- Restrict real parabolic homomorphisms along an inclusion of subgroups. -/
def realParabolicHoms_restrict {H Γ : Subgroup SL(2, ℤ)} (h : H ≤ Γ) :
    parabolicHoms ℝ Γ ℝ →ₗ[ℝ] parabolicHoms ℝ H ℝ where
  toFun φ := ⟨(φ : Additive Γ →+ ℝ).comp (Subgroup.inclusion h).toAdditive, by
    intro γ hγ
    exact φ.property (Subgroup.inclusion h γ) hγ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The defining period integral commutes with restriction. -/
theorem periodOf_restrict {H Γ : Subgroup SL(2, ℤ)} (h : H ≤ Γ)
    (f : CuspForm Γ 2) (γ : H) :
    periodOf H γ (weightTwoCuspForms_restrict h f) =
      periodOf Γ (Subgroup.inclusion h γ) f := rfl

/-- The real period maps form a commuting square under restriction. -/
theorem realPeriods_restrict {H Γ : Subgroup SL(2, ℤ)} [H.FiniteIndex] [Γ.FiniteIndex]
    (h : H ≤ Γ) (f : CuspForm Γ 2) :
    realPeriods H (weightTwoCuspForms_restrict h f) =
      realParabolicHoms_restrict h (realPeriods Γ f) := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro γ
  change (realPeriods H (weightTwoCuspForms_restrict h f) : Additive H →+ ℝ)
      (Additive.ofMul (Additive.toMul γ)) = _
  rw [realPeriods_apply]
  change (periodOf H _ _).re = (realPeriods Γ f : Additive Γ →+ ℝ)
    (Additive.ofMul (Subgroup.inclusion h (Additive.toMul γ)))
  rw [realPeriods_apply, periodOf_restrict]

/-- A real homomorphism is determined by its values on a finite-index subgroup. -/
theorem realParabolicHoms_restrict_injective {H Γ : Subgroup SL(2, ℤ)} [H.FiniteIndex]
    (h : H ≤ Γ) : Function.Injective (realParabolicHoms_restrict h) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro φ hφ
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro γ
  let g : Γ := Additive.toMul γ
  obtain ⟨n, hn, _, hgn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := H)) (g : SL(2, ℤ))
  have heval := congrArg
    (fun ψ : parabolicHoms ℝ H ℝ => (ψ : Additive H →+ ℝ)
      (Additive.ofMul ⟨(g : SL(2, ℤ)) ^ n, hgn⟩)) hφ
  have hp : (φ : Additive Γ →+ ℝ) (Additive.ofMul (g ^ n)) = 0 := heval
  rw [ofMul_pow, map_nsmul] at hp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpzero : (φ : Additive Γ →+ ℝ) (Additive.ofMul g) = 0 :=
    (mul_eq_zero.mp (by simpa only [nsmul_eq_mul] using hp)).resolve_left hnR
  simpa [g] using hpzero

end WeightTwoCusps
