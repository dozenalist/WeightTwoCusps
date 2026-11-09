/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "adicValuation toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem rowMain : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete :=
  AlgebraicCurve.Place.rowMain v


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.lean. -/
@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.Place.adicValuation_isRankOneDiscrete {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.solution

