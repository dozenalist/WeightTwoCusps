module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 114

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(38z) η(57z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(38z) η(57z)` at level 114. -/
abbrev cuspForm_114_eta_1m2_2p3_3p3_6m2_38p1_57p1 : gamma0CuspForms 114 :=
  etaQuotientCuspForm 114 sparse![114; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 37 => 1, 56 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1m2_2p3_3p3_6m2_38p1_57p1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1m2_2p3_3p3_6m2_38p1_57p1 =
    [0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -3, -2, -3, 1, 1, -2, 1,
     -3, -1, -1, -1, 0, -3, 1, 0, -2, 1, 1, 2, -1, 0, 0, -3, 1, 0, 0, -1,
     3, 3, 0, -3, 0, 2, 0, 2, -3, -1, -1, 4, 4, 2, 0, 3, 3, -1, 4, 0,
     1, 1, 1, 1, -3, 1, 4, -1, -2, -3, 1, 1, 3, 1, -1, 5, -1, 3, -3, -1,
     1, 0, 0, -8, 2, -3, 1, -4, -2, 3, -6, 6, -1, -5, 0, -1, 4, -1, -2, 1] := by
  eta_coeff

end WeightTwoCusps
