/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Mathlib.NumberTheory.RatFunc.Ostrowski
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_Place_adicValuation_isTrivialOn
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes
public import Mathlib.FieldTheory.RatFunc.Valuation

@[expose] public section
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
p2m_erase_attrs «simp» AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := by
  haveI := v.adicValuation_isRankOneDiscrete
  haveI := v.adicValuation_isTrivialOn
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)
  · obtain ⟨w, hw, -⟩ := h
    exact absurd (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))) (hv w)


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.lean. -/
@[expose] public section
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
p2m_erase_attrs «simp» AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.solution

