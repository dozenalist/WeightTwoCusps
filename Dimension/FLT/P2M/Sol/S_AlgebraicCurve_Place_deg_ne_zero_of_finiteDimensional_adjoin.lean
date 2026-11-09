/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_deg_ne_zero
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
p2m_erase_attrs «simp» AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) : v.deg ≠ 0 := by
  classical

  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) := transcendental_iff_injective.mp hx
  let lift : RatFunc K →ₐ[K] F :=
    RatFunc.liftAlgHom (Polynomial.aeval x) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  have hlift : ∀ p : Polynomial K, lift (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval x p := fun p => by
    have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval x)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj) p 1
    rwa [map_one, div_one, map_one, div_one] at h
  letI : Algebra (RatFunc K) F := lift.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq' (lift.comp_algebraMap).symm
  haveI hFD : FiniteDimensional (RatFunc K) F := by
    obtain ⟨s, hs⟩ := Module.finite_def.mp ‹FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F›
    refine ⟨⟨s, ?_⟩⟩
    rw [eq_top_iff]
    rintro z -
    have hz : z ∈ Submodule.span (IntermediateField.adjoin K ({x} : Set F)) (s : Set F) := by
      rw [hs]; trivial
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c y _ hy =>
        have hrange : IntermediateField.adjoin K ({x} : Set F) ≤ lift.fieldRange := by
          rw [IntermediateField.adjoin_le_iff]
          rintro y' rfl
          exact ⟨algebraMap (Polynomial K) (RatFunc K) Polynomial.X, (hlift _).trans (Polynomial.aeval_X _)⟩
        obtain ⟨c', hc'⟩ := hrange c.2
        have hcc : c • y = c' • y := by
          change (c : F) * y = lift.toRingHom c' * y
          rw [← hc']
        rw [hcc]
        exact Submodule.smul_mem _ c' hy
  have h1 := AlgebraicCurve.RationalFunctionField.deg_ne_zero (v.restrict (RatFunc K))
  have h2 := AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional (F := RatFunc K) v
  rw [← AlgebraicCurve.Place.deg_restrict_mul_inertiaDeg (F := RatFunc K)]
  exact mul_ne_zero h1 h2.ne'


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin.lean. -/
@[expose] public section
p2m_erase_attrs «instance» AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
p2m_erase_attrs «simp» AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

theorem AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) : v.deg ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin.solution

