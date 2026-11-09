/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
p2m_erase_attrs «simp» AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord (algebraMap (Polynomial K) (RatFunc K) p) = 1 := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  rw [AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log w hp hw
    (RatFunc.algebraMap_ne_zero hp), hval]
  simp [log_exp]


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span.lean. -/
@[expose] public section
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
p2m_erase_attrs «simp» AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_of_span {K : Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord (algebraMap (Polynomial K) (RatFunc K) p) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span.solution

