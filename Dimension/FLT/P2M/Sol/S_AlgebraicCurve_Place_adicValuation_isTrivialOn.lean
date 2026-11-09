/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_Place_adicValuation_isTrivialOn.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Place_adicValuation_isTrivialOn

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext heightOneSpectrum adicValuation algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.adicValuation_valuationSubring :
    v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (⟨x, hx⟩ : v.toValuationSubring)

p2m_export "AlgebraicCurve.Place" "adicValuation_valuationSubring"
private theorem _root_.AlgebraicCurve.Place.mem_iff_adicValuation_le_one {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  rw [← v.adicValuation_valuationSubring]
  exact Valuation.mem_valuationSubring_iff _ _

p2m_export "AlgebraicCurve.Place" "mem_iff_adicValuation_le_one"
private theorem rowMain : v.adicValuation.IsTrivialOn K :=
  Valuation.IsTrivialOn.of_le_one v.adicValuation fun a =>
    v.mem_iff_adicValuation_le_one.mp (v.algebraMap_mem' a)

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_adicValuation_isTrivialOn.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsTrivialOn K :=
  AlgebraicCurve.Place.rowMain v


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_Place_adicValuation_isTrivialOn.lean. -/
@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.Place.adicValuation_isTrivialOn {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsTrivialOn K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_adicValuation_isTrivialOn.solution

