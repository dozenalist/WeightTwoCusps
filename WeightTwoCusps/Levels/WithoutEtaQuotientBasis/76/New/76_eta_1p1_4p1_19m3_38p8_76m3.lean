module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 76

The eta expression is `η(z) η(4z) η(19z)^(-3) η(38z)^8 η(76z)^(-3)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-76).
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

/-- The cuspidal eta quotient `η(z) η(4z) η(19z)^(-3) η(38z)^8 η(76z)^(-3)` at level 76. -/
abbrev cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3 : gamma0CuspForms 76 :=
  etaQuotientCuspForm 76 sparse![76; 0 => 1, 3 => 1, 18 => -3, 37 => 8, 75 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3_first_coeffs :
    first_coeffs 100 cuspForm_76_eta_1p1_4p1_19m3_38p8_76m3 =
    [0, 1, -1, -1, 0, -1, 2, 1, 1, -1, 0, 1, -1, -1, -1, 0, -2, 1, 0, 0,
     4, -1, -4, 0, -2, 6, 4, 3, -2, 1, 2, -6, -3, -4, 1, -7, 2, 0, 0, 4,
     6, -6, 0, 3, 2, 5, 1, 3, 3, -2, -9, 1, -3, 3, -6, -1, -3, 0, 0, 7,
     -6, -1, 6, -3, 2, -2, 4, 1, -4, 1, 8, 2, 2, 1, 0, -9, 1, 3, -5, -4,
     -2, -3, 8, 0, 3, -9, 0, 0, 2, 2, -6, -1, 0, 6, -2, 3, 6, 0, 2, 1] := by
  eta_coeff

end WeightTwoCusps
