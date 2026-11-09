module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 114

The eta expression is `η(z) η(3z)^(-1) η(6z)^2 η(38z) η(57z)^2 η(114z)^(-1)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-114).
The table has full eta basis = NO at this level: these supporting forms
do not span the whole cusp-form space.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(3z)^(-1) η(6z)^2 η(38z) η(57z)^2 η(114z)^(-1)` at level 114. -/
abbrev cuspForm_114_eta_1p1_3m1_6p2_38p1_57p2_114m1 : gamma0CuspForms 114 :=
  etaQuotientCuspForm 114 sparse![114; 0 => 1, 2 => -1, 5 => 2, 37 => 1, 56 => 2, 113 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1p1_3m1_6p2_38p1_57p2_114m1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1p1_3m1_6p2_38p1_57p2_114m1 =
    [0, 0, 1, -1, -1, 1, -1, 0, 0, 1, 1, 1, 0, -1, -1, 0, 1, -2, 1, 0,
     0, -1, -1, -1, 1, 1, -1, 2, 1, 0, 0, 1, 0, 0, -1, -1, 0, 1, 0, 1,
     -2, 1, 1, -1, 0, -1, 0, -1, -2, -2, 0, 0, 2, 1, 1, 1, 0, 0, 1, -1,
     2, 3, -2, 1, 1, -1, -4, -4, -1, 0, 3, 3, 0, 0, 4, -4, 0, -1, 2, 2,
     2, -4, -2, 4, -4, -3, 1, -1, -4, 3, -1, 3, -1, 4, -3, 0, -3, 5, 0, -1] := by
  eta_coeff

end WeightTwoCusps
