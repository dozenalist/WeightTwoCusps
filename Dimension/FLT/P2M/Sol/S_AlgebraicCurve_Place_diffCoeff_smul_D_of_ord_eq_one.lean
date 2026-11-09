/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
public import Dimension.FLT.P2M.Sol.S_KaehlerDifferential_span_D_eq_top_of_transcendental
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_Differentials

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
p2m_erase_attrs «simp» AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

noncomputable section

private theorem exists_eq_smul_D {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    (x : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) (ω : Ω[F⁄K]) :
    ∃ g : F, ω = g • KaehlerDifferential.D K F t := by
  haveI := AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one x v ht
  have hspan := KaehlerDifferential.span_D_eq_top_of_transcendental K t
    (v.transcendental_of_ord_ne_zero (ht ▸ one_ne_zero))
  have hω : ω ∈ Submodule.span F {KaehlerDifferential.D K F t} := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hω
  exact ⟨g, hg.symm⟩

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) (ω : Ω[F⁄K]) :
    AlgebraicCurve.Place.diffCoeff t ω • KaehlerDifferential.D K F t = ω :=
  AlgebraicCurve.Place.diffCoeff_smul_D (exists_eq_smul_D x v ht ω)

end


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean. -/
@[expose] public section
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
p2m_erase_attrs «simp» AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

theorem AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) (ω : Ω[F⁄K]) :
    AlgebraicCurve.Place.diffCoeff t ω • KaehlerDifferential.D K F t = ω := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.solution

