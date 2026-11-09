/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_RationalFunctionField_deg_ne_zero.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ne_zero
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
p2m_erase_attrs «simp» AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve IsDedekindDomain Polynomial

theorem solution {K : Type*} [Field K] (v : Place K (RatFunc K)) : v.deg ≠ 0 := by
  by_cases h : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w
  · rw [RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum v h]
    exact one_ne_zero
  · obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w := by
      simpa using h
    subst hw
    obtain ⟨p, hp⟩ := Submodule.IsPrincipal.principal w.asIdeal
    rw [RationalFunctionField.deg_ofHeightOneSpectrum K hp]
    have hp0 : p ≠ 0 := by
      intro h0
      apply w.ne_bot
      rw [hp, h0]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    have hprime : Prime p := by
      have hpr := w.isPrime
      rw [hp] at hpr
      exact (Ideal.span_singleton_prime hp0).mp hpr
    exact (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hprime.irreducible)).ne'


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_ne_zero.lean. -/
@[expose] public section
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
p2m_erase_attrs «simp» AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.deg_ne_zero {K : Type*} [Field K] (v : Place K (RatFunc K)) : v.deg ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ne_zero.solution

