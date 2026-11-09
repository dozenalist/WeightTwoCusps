module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 114

The eta expression is `η(z)^2 η(2z)^(-1) η(6z) η(19z)^(-1) η(38z)^2 η(57z)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(6z) η(19z)^(-1) η(38z)^2 η(57z)` at level 114. -/
abbrev cuspForm_114_eta_1p2_2m1_6p1_19m1_38p2_57p1 : gamma0CuspForms 114 :=
  etaQuotientCuspForm 114 sparse![114; 0 => 2, 1 => -1, 5 => 1, 18 => -1, 37 => 2, 56 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1p2_2m1_6p1_19m1_38p2_57p1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1p2_2m1_6p1_19m1_38p2_57p1 =
    [0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, -1, 2, 0, -2, -2, 0, -1, 2, 0,
     2, 0, 0, 0, 1, -2, 2, -2, 2, 0, -3, 2, 0, -4, -2, 1, -1, 2, 0, 4,
     0, 2, 2, 0, -2, 2, -2, -1, -2, -2, 0, 4, -2, -2, -1, 0, -2, 0, 2, 0,
     2, 2, 0, 0, 0, 0, 1, -2, 0, 2, 4, 2, -4, -2, 0, -4, 0, -1, 2, 0,
     0, -5, 4, 2, -2, 0, 0, 1, 0, 0, 4, 0, 2, -1, -4, -1, -3, 2, 2, 0] := by
  eta_coeff

end WeightTwoCusps
