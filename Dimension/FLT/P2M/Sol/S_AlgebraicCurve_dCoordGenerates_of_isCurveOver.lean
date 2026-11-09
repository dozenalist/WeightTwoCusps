/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_dCoordGenerates_of_isCurveOver.lean.
Adapted for this project: shared canonical-divisor and local-coordinate proof.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver

public import Dimension.FLT.EndScopes
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_IsCurveOver
public import Dimension.FLT.Definitions.Def_ModularCurve_CanonicalDivisor
public import Dimension.FLT.P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicCurve_dCoordGenerates_of_isCurveOver


theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :
    ∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates :=
  _root_.P2MW.S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.shared_dCoordGenerates


flt_end_scopes

@[expose] public section

namespace AlgebraicCurve

theorem dCoordGenerates_of_isCurveOver {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∀ v : Place K F, v.DCoordGenerates := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_dCoordGenerates_of_isCurveOver.solution

