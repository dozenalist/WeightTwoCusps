/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeInfty.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation

@[expose] public section
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty
p2m_erase_attrs «instance» AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
p2m_erase_attrs «simp» AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem solution {K : Type*} [Field K] [DecidableEq (RatFunc K)] {f : RatFunc K} (hf : f ≠ 0) : (placeInfty K).ord f = -f.intDegree :=
  AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum (placeInfty K)
    (AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K) hf


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty.lean. -/
@[expose] public section
p2m_erase_attrs «instance» AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
p2m_erase_attrs «simp» AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.ord_placeInfty {K : Type*} [Field K] [DecidableEq (RatFunc K)] {f : RatFunc K} (hf : f ≠ 0) : (placeInfty K).ord f = -f.intDegree := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty.solution

