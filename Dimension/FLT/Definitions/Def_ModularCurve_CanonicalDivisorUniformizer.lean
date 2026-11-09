/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_CanonicalDivisorUniformizer.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.MathlibImports
public import Dimension.FLT.Definitions.Def_ModularCurve_CanonicalDivisor

@[expose] public section

set_option autoImplicit false

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem dCoord_eq : v.dCoord = KaehlerDifferential.D K F v.uniformizer := rfl

end Place

end AlgebraicCurve

end
