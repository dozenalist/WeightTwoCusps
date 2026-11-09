module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 92

The eta expression is `η(z) η(2z)^(-1) η(4z)^2 η(23z) η(46z)^(-1) η(92z)^2`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-92).
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

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(4z)^2 η(23z) η(46z)^(-1) η(92z)^2` at level 92. -/
abbrev cuspForm_92_eta_1p1_2m1_4p2_23p1_46m1_92p2 : gamma0CuspForms 92 :=
  etaQuotientCuspForm 92 sparse![92; 0 => 1, 1 => -1, 3 => 2, 22 => 1, 45 => -1, 91 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_92_eta_1p1_2m1_4p2_23p1_46m1_92p2_first_coeffs :
    first_coeffs 100 cuspForm_92_eta_1p1_2m1_4p2_23p1_46m1_92p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, -1, 1, 1, 1, -1, 1, 0, 1, 0,
     0, -2, -1, 0, 0, -1, 1, 1, -2, 0, -1, 1, 1, 2, 1, 1, -1, 0, 0, -2,
     0, 0, -1, 0, 2, 2, 0, -1, 0, -1, -2, 1, -1, 0, 0, -1, 0, 0, -1, 0,
     0, 0, 0, 2, -1, 0, 1, -1, 0, 0, 4, 2, -1, 1, 1, 1, 0, -1, 0, 0,
     0, -3, -1, -3, 2, 1, -2, -1, 2, -2, 2, -1, 0, -3, 0, 0, -2, 2, -2, -2] := by
  eta_coeff

end WeightTwoCusps
