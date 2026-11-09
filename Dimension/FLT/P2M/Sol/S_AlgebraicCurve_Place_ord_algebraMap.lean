/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_Place_ord_algebraMap.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Place_ord_algebraMap

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "coe_algebraMap adicValuation adicValuation_coe_eq_one_iff ord ord_zero toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.isUnit_algebraMap {c : K} (hc : c ≠ 0) :
    IsUnit (algebraMap K v.toValuationSubring c) :=
  (isUnit_iff_ne_zero.mpr hc).map _

p2m_export "AlgebraicCurve.Place" "isUnit_algebraMap"
private theorem _root_.AlgebraicCurve.Place.adicValuation_algebraMap {c : K} (hc : c ≠ 0) :
    v.adicValuation (algebraMap K F c) = 1 := by
  rw [← v.coe_algebraMap]
  exact (v.adicValuation_coe_eq_one_iff _).mpr (v.isUnit_algebraMap hc)

p2m_export "AlgebraicCurve.Place" "adicValuation_algebraMap"
private theorem rowMain (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, v.ord_zero]
  · simp only [ord, v.adicValuation_algebraMap hc, log_one, neg_zero]

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_ord_algebraMap.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 :=
  AlgebraicCurve.Place.rowMain v c


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_Place_ord_algebraMap.lean. -/
@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.Place.ord_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_algebraMap.solution

