/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.Definitions.Def_AlgebraicCurve_Correspondence
public import Mathlib.FieldTheory.Galois.Basic
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_SemilinearAut_inertiaDeg_smul
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorPushPull

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
p2m_erase_attrs «simp» AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

set_option autoImplicit false
noncomputable section
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.AlgebraicCurve IsDedekindDomain"
open scoped Pointwise

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "SemilinearAut.IntertwinesAlong Place SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.ofAlgAut_smul Place.exists_algEquiv_smul_eq_of_restrict_eq SemilinearAut.inertiaDeg_smul"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrict inertiaDeg exists_algEquiv_smul_eq_of_restrict_eq"
p2m_open "AlgebraicCurve.Place"

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

private theorem intertwinesAlong_one_ofAlgAut (σ : M ≃ₐ[F'] M) :
    SemilinearAut.IntertwinesAlong (algebraMap F' M) (1 : SemilinearAut K F')
      (SemilinearAut.ofAlgAut (σ.restrictScalars K)) := by
  intro x
  rw [one_smul, SemilinearAut.ofAlgAut_smul]
  exact σ.commutes x

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.AlgebraicCurve.Place in
theorem solution {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    W'.inertiaDeg F' = W.inertiaDeg F' := by
  obtain ⟨σ, rfl⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq W W' h
  exact SemilinearAut.inertiaDeg_smul (intertwinesAlong_one_ofAlgAut σ) W

end


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.lean. -/
@[expose] public section
p2m_erase_attrs «instance» AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
p2m_erase_attrs «simp» AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve
theorem AlgebraicCurve.Place.inertiaDeg_eq_of_restrict_eq {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    W'.inertiaDeg F' = W.inertiaDeg F' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.solution

