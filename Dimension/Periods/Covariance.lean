module

public import Dimension.Periods.Restriction

/-! # Covariance of weight-two periods under the modular slash action -/

@[expose] public section

open scoped MatrixGroups ModularForm
open UpperHalfPlane

noncomputable section

namespace WeightTwoCusps

def normalSlash (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] [H.Normal]
    (f : CuspForm H 2) (γ : SL(2, ℤ)) : CuspForm H 2 where
  toFun := (f : ℍ → ℂ) ∣[(2 : ℤ)] γ
  slash_action_eq' g hg := by
    obtain ⟨δ, hδ, rfl⟩ := hg
    change ((f : ℍ → ℂ) ∣[(2 : ℤ)] γ) ∣[(2 : ℤ)] δ = (f : ℍ → ℂ) ∣[(2 : ℤ)] γ
    rw [← SlashAction.slash_mul]
    have heq : γ * δ = (γ * δ * γ⁻¹) * γ := by group
    rw [heq, SlashAction.slash_mul]
    have hf : (f : ℍ → ℂ) ∣[(2 : ℤ)] (γ * δ * γ⁻¹) = f :=
      SlashInvariantFormClass.slash_action_eq f _ ⟨_, (inferInstance : H.Normal).conj_mem δ hδ γ, rfl⟩
    rw [hf]
  holo' := f.holo'.slash 2 _
  zero_at_cusps' {c} hc := by
    apply (CuspForm.translate f (γ : GL (Fin 2) ℝ)).zero_at_cusps'
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    have hsmul : IsCusp ((γ : GL (Fin 2) ℝ) • c) (H : Subgroup (GL (Fin 2) ℝ)) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact hc.smul_of_mem ⟨γ, rfl⟩
    simpa [mul_smul] using hsmul.smul (γ : GL (Fin 2) ℝ)⁻¹

open ModularCurve ModularCurve.Period

theorem periodOf_normalSlash (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] [H.Normal]
    (f : CuspForm H 2) (γ : SL(2, ℤ)) (δ : H) :
    periodOf H δ (normalSlash H f γ) =
      periodOf H ⟨γ * δ * γ⁻¹, (inferInstance : H.Normal).conj_mem δ δ.property γ⟩ f := by
  obtain ⟨F, hF⟩ := exists_hasEquivariantPrimitiveOf H f
  have hderiv : ∀ τ : ℍ,
      HasDerivAt ((fun z => F (γ • z)) ∘ ofComplex) (normalSlash H f γ τ) ↑τ := by
    intro τ
    exact P2MW.S_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero.ModularCurve.PeriodRealInjectivityOf.hasDerivAt_comp_smul
      hF.1 γ τ
  change periodAlongOf H I ((δ : SL(2, ℤ)) • I) (normalSlash H f γ) = _
  rw [P2MW.S_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf.ModularCurve.PeriodFTCOf.periodAlongOf_eq_sub
    H (normalSlash H f γ) hderiv I ((δ : SL(2, ℤ)) • I)]
  rw [periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf H f hF]
  have h := hF.2.2.1.sub_eq_period
    (⟨γ * δ * γ⁻¹, (inferInstance : H.Normal).conj_mem δ δ.property γ⟩ : H) (γ • I)
  simpa [IsEquivariantPrimitive.period, mul_smul] using h

end WeightTwoCusps
