module

public import Dimension.FLT.P2M.Sol.S_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero
public import Dimension.FLT.P2M.Sol.S_ModularCurve_periodMapOf_mem_parabolicHoms
public import Dimension.FLT.P2M.Sol.S_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp
@[expose] public section

/-!
# Comparing cusp forms with integral parabolic homomorphisms

The real parts of the periods give an injective real linear map from weight-two
cusp forms to real parabolic homomorphisms. An integral basis of parabolic
homomorphisms stays a basis over the reals. Consequently twice the complex
dimension of cusp forms is at most the integral rank of parabolic homomorphisms.

The analytic injectivity, integral basis, and rank calculation are copied with
attribution under `Dimension/FLT`. The comparison below supplies the upper bound;
`Dimension.Relation` combines it with the Riemann--Roch lower bound.
-/

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

open ModularCurve ModularCurve.Period

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

private theorem periodMapOf_apply_eq_periodOf (f : CuspForm Γ 2) (γ : Γ) :
    periodMapOf Γ f (Additive.ofMul γ) = periodOf Γ γ f := by
  obtain ⟨F, hF⟩ := exists_hasEquivariantPrimitiveOf Γ f
  obtain ⟨F₀, h₀, hp⟩ := periodMapOf_def Γ f hF
  rw [hp, IsEquivariantPrimitive.periodHom_apply,
    periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf Γ f h₀ γ]
  rfl

private theorem periodMapOf_apply_additive (f : CuspForm Γ 2) (γ : Additive Γ) :
    periodMapOf Γ f γ = periodOf Γ (Additive.toMul γ) f := by
  simpa only [ofMul_toMul] using
    periodMapOf_apply_eq_periodOf Γ f (Additive.toMul γ)

/-- The real parts of the periods, regarded as a real parabolic homomorphism. -/
def realPeriods : CuspForm Γ 2 →ₗ[ℝ] parabolicHoms ℝ Γ ℝ where
  toFun f := ⟨Complex.reLm.toAddMonoidHom.comp (periodMapOf Γ f), by
    intro γ hγ
    exact congrArg Complex.re ((periodMapOf_mem_parabolicHoms Γ f) γ hγ)⟩
  map_add' f g := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro γ
    change (periodMapOf Γ (f + g) γ).re =
      (periodMapOf Γ f γ).re + (periodMapOf Γ g γ).re
    rw [periodMapOf_apply_additive, periodMapOf_apply_additive,
      periodMapOf_apply_additive, map_add, Complex.add_re]
  map_smul' r f := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro γ
    change (periodMapOf Γ (r • f) γ).re = r * (periodMapOf Γ f γ).re
    rw [periodMapOf_apply_additive, periodMapOf_apply_additive]
    exact ((Complex.reLm).comp ((periodOf Γ (Additive.toMul γ)).restrictScalars ℝ)).map_smul r f

@[simp]
theorem realPeriods_apply (f : CuspForm Γ 2) (γ : Γ) :
    (realPeriods Γ f : Additive Γ →+ ℝ) (Additive.ofMul γ) = (periodOf Γ γ f).re :=
  congrArg Complex.re (periodMapOf_apply_eq_periodOf Γ f γ)

/-- A weight-two cusp form is determined by the real parts of all its periods. -/
theorem realPeriods_injective : Function.Injective (realPeriods Γ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  apply eq_zero_of_forall_re_periodOf_eq_zero Γ f
  intro γ
  have h := congrArg
    (fun φ : parabolicHoms ℝ Γ ℝ ↦ (φ : Additive Γ →+ ℝ) (Additive.ofMul γ)) hf
  simpa only [realPeriods_apply, Submodule.coe_zero, AddMonoidHom.zero_apply] using h

instance finiteDimensional_realParabolicHoms :
    FiniteDimensional ℝ (parabolicHoms ℝ Γ ℝ) := by
  obtain ⟨n, b, hb⟩ := exists_basis_parabolicHoms_castAddHom_comp Γ
  obtain ⟨bℝ, _⟩ := hb ℝ
  exact Module.Finite.of_basis bℝ

/-- Finite-dimensionality follows already from real period injectivity. -/
instance finiteDimensional_weightTwoCuspForms : FiniteDimensional ℂ (CuspForm Γ 2) := by
  letI : FiniteDimensional ℝ (CuspForm Γ 2) :=
    Module.Finite.of_injective (realPeriods Γ) (realPeriods_injective Γ)
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ (CuspForm Γ 2)

/-- Real and integral parabolic homomorphisms have the same rank. -/
theorem realParabolicHoms_finrank_eq_int :
    Module.finrank ℝ (parabolicHoms ℝ Γ ℝ) =
      Module.finrank ℤ (parabolicHoms ℤ Γ ℤ) := by
  obtain ⟨n, b, hb⟩ := exists_basis_parabolicHoms_castAddHom_comp Γ
  obtain ⟨bℝ, _⟩ := hb ℝ
  rw [Module.finrank_eq_card_basis bℝ, Module.finrank_eq_card_basis b]

/-- Changing the characteristic-zero coefficient field preserves parabolic rank. -/
theorem realParabolicHoms_finrank_eq_rat :
    Module.finrank ℝ (parabolicHoms ℝ Γ ℝ) =
      Module.finrank ℚ (parabolicHoms ℚ Γ ℚ) := by
  obtain ⟨n, b, hb⟩ := exists_basis_parabolicHoms_castAddHom_comp Γ
  obtain ⟨bℝ, _⟩ := hb ℝ
  obtain ⟨bℚ, _⟩ := hb ℚ
  rw [Module.finrank_eq_card_basis bℝ, Module.finrank_eq_card_basis bℚ]

/-- The real period injection bounds twice the complex cusp-form dimension. -/
theorem two_mul_finrank_cuspForms_le_intParabolicHoms :
    2 * Module.finrank ℂ (CuspForm Γ 2) ≤
      Module.finrank ℤ (parabolicHoms ℤ Γ ℤ) := by
  rw [← finrank_real_of_complex, ← realParabolicHoms_finrank_eq_int Γ]
  exact LinearMap.finrank_le_finrank_of_injective (realPeriods_injective Γ)

end WeightTwoCusps
