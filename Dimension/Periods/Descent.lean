module

public import Dimension.Periods.Covariance
public import Dimension.Gamma.PeriodIsomorphism

/-!
# Descent of the real period isomorphism

An equivariant real period on a normal subgroup determines a cusp form invariant
under the larger group. This descends the principal-level period isomorphism
to congruence subgroups containing that principal group.
-/

@[expose] public section

noncomputable section

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace WeightTwoCusps

open ModularCurve ModularCurve.Period

/-- Surjectivity of periods descends from a finite-index normal subgroup. -/
theorem realPeriods_surjective_of_normal_subgroup {H Γ : Subgroup SL(2, ℤ)}
    [H.FiniteIndex] [H.Normal] [Γ.FiniteIndex] (h : H ≤ Γ)
    (hs : Function.Surjective (realPeriods H)) : Function.Surjective (realPeriods Γ) := by
  intro φ
  obtain ⟨f, hf⟩ := hs (realParabolicHoms_restrict h φ)
  have hres (δ : H) : (periodOf H δ f).re =
      (φ : Additive Γ →+ ℝ) (Additive.ofMul (Subgroup.inclusion h δ)) := by
    have he := congrArg
      (fun ψ : parabolicHoms ℝ H ℝ => (ψ : Additive H →+ ℝ) (Additive.ofMul δ)) hf
    simpa [realPeriods_apply, realParabolicHoms_restrict] using he
  have hinvariant (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) : normalSlash H f γ = f := by
    apply realPeriods_injective H
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro δ
    change (realPeriods H (normalSlash H f γ) : Additive H →+ ℝ)
      (Additive.ofMul (Additive.toMul δ)) =
      (realPeriods H f : Additive H →+ ℝ) (Additive.ofMul (Additive.toMul δ))
    rw [realPeriods_apply, realPeriods_apply, periodOf_normalSlash, hres, hres]
    let g : Γ := ⟨γ, hγ⟩
    let d : Γ := Subgroup.inclusion h (Additive.toMul δ)
    change (φ : Additive Γ →+ ℝ) (Additive.ofMul (g * d * g⁻¹)) =
      (φ : Additive Γ →+ ℝ) (Additive.ofMul d)
    simp only [ofMul_mul, ofMul_inv, map_add, map_neg]
    abel
  let fΓ : CuspForm Γ 2 := {
    toFun := f
    slash_action_eq' := by
      intro g hg
      obtain ⟨γ, hγ, rfl⟩ := hg
      exact congrArg (fun F : CuspForm H 2 => (F : ℍ → ℂ)) (hinvariant γ hγ)
    holo' := f.holo'
    zero_at_cusps' := by
      intro c hc
      apply f.zero_at_cusps'
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact hc }
  refine ⟨fΓ, ?_⟩
  apply realParabolicHoms_restrict_injective h
  rw [← realPeriods_restrict h fΓ]
  have heq : weightTwoCuspForms_restrict h fΓ = f := DFunLike.ext _ _ fun _ => rfl
  rw [heq]
  exact hf

/-- Every real parabolic homomorphism on a congruence group is a real period. -/
theorem realPeriods_surjective_of_Gamma_le (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (h : CongruenceSubgroup.Gamma N ≤ Γ) :
    Function.Surjective (realPeriods Γ) := by
  letI := CongruenceSubgroup.Gamma_normal N
  exact realPeriods_surjective_of_normal_subgroup h (principal_realPeriods_bijective N hN).2

/-- The complete weight-two period isomorphism for a congruence group. -/
def realPeriodEquiv_of_Gamma_le (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (h : CongruenceSubgroup.Gamma N ≤ Γ) :
    CuspForm Γ 2 ≃ₗ[ℝ] parabolicHoms ℝ Γ ℝ :=
  LinearEquiv.ofBijective (realPeriods Γ)
    ⟨realPeriods_injective Γ, realPeriods_surjective_of_Gamma_le Γ N hN h⟩

/-- Twice the complex dimension is the rational parabolic rank. -/
theorem two_mul_finrank_cuspForms_eq_parabolicHoms_of_Gamma_le
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (h : CongruenceSubgroup.Gamma N ≤ Γ) :
    2 * Module.finrank ℂ (CuspForm Γ 2) =
      Module.finrank ℚ (parabolicHoms ℚ Γ ℚ) := by
  have hd := (realPeriodEquiv_of_Gamma_le Γ N hN h).finrank_eq
  rw [finrank_real_of_complex, realParabolicHoms_finrank_eq_rat] at hd
  exact hd

end WeightTwoCusps
