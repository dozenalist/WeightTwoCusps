module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 138

The eta expression is `η(z) η(2z)^(-1) η(3z)^(-1) η(6z)^3 η(23z) η(46z)^(-1) η(69z)^(-1) η(138z)^3`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-138).
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

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(3z)^(-1) η(6z)^3 η(23z) η(46z)^(-1) η(69z)^(-1) η(138z)^3` at level 138. -/
abbrev cuspForm_138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3 : gamma0CuspForms 138 :=
  etaQuotientCuspForm 138 sparse![138; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 22 => 1, 45 => -1, 68 => -1, 137 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3_first_coeffs :
    first_coeffs 100 cuspForm_138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, -1,
     -1, 1, 1, 0, 0, 1, -1, 1, -1, 0, 1, 1, 0, 0, -1, -1, -1, -1, 1, 0,
     0, 1, 0, 1, 0, -2, 0, 0, -1, 0, -1, 1, 1, 0, 0, 0, 1, 0, 1, 2,
     0, -1, 0, 0, 0, 0, -1, -1, 1, 0, 1, 0, 2, 0, 0, -1, -2, -3, 0, -2,
     1, 0, -2, 0, 2, 1, -1, 0, 1, 0, 0, 2, 0, -1, -1, -1, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
