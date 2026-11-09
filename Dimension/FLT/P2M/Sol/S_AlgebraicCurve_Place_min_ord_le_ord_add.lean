/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_Place_min_ord_le_ord_add.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Place_min_ord_le_ord_add

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord"
namespace FF2S
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem le_ord_add (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hfg' := v.adicValuation_ne_zero hfg
  have hmax : v.adicValuation (f + g) ≤ max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add _ _ _
  unfold Place.ord
  rcases le_max_iff.mp hmax with hle | hle
  · have := (WithZero.log_le_log hfg' hf').mpr hle
    omega
  · have := (WithZero.log_le_log hfg' hg').mpr hle
    omega

end AlgebraicCurve.FF2S

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) :=
  AlgebraicCurve.FF2S.le_ord_add v hf hg hfg


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_Place_min_ord_le_ord_add.lean. -/
@[expose] public section

theorem AlgebraicCurve.Place.min_ord_le_ord_add {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_min_ord_le_ord_add.solution

