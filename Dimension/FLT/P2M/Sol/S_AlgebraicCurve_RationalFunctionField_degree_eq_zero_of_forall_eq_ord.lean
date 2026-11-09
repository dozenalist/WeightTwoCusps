/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
p2m_erase_attrs «simp» AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] {f : RatFunc K} (D : Divisor K (RatFunc K)) (hD : ∀ v : Place K (RatFunc K), D v = v.ord f) : Divisor.degree D = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  · have hden : f.denom ≠ 0 := f.denom_ne_zero
    have hdenF : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := RatFunc.algebraMap_ne_zero hden

    set Dden : Divisor K (RatFunc K) :=
      Finsupp.ofSupportFinite
        (fun v : Place K (RatFunc K) => v.ord (algebraMap K[X] (RatFunc K) f.denom))
        (AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero hdenF) with hDden_def
    have hDden : ∀ v : Place K (RatFunc K),
        Dden v = v.ord (algebraMap K[X] (RatFunc K) f.denom) := fun v => rfl
    have hsplit : ∀ v : Place K (RatFunc K),
        (D + Dden) v = v.ord (algebraMap K[X] (RatFunc K) f.num) := by
      intro v
      rw [Finsupp.add_apply, hD v, hDden v]
      have hmul : f * algebraMap K[X] (RatFunc K) f.denom
          = algebraMap K[X] (RatFunc K) f.num :=
        ((div_eq_iff hdenF).mp f.num_div_denom).symm
      have h2 := v.ord_mul hf hdenF
      rw [hmul] at h2
      exact h2.symm
    have h1 := AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap
      f.num (D + Dden) hsplit
    have h2 := AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap
      f.denom Dden hDden
    rw [map_add, h2, add_zero] at h1
    exact h1


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean. -/
@[expose] public section
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
p2m_erase_attrs «simp» AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord {K : Type*} [Field K] {f : RatFunc K} (D : Divisor K (RatFunc K)) (hD : ∀ v : Place K (RatFunc K), D v = v.ord f) : Divisor.degree D = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.solution

