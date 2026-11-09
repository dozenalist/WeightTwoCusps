module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 225

The eta expression is `η(z) η(3z)^(-1) η(5z)^(-1) η(9z) η(15z)^4 η(25z) η(45z)^(-1) η(75z)^(-1) η(225z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-225).
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

/-- The cuspidal eta quotient `η(z) η(3z)^(-1) η(5z)^(-1) η(9z) η(15z)^4 η(25z) η(45z)^(-1) η(75z)^(-1) η(225z)` at level 225. -/
abbrev cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1 : gamma0CuspForms 225 :=
  etaQuotientCuspForm 225 sparse![225; 0 => 1, 2 => -1, 4 => -1, 8 => 1, 14 => 4, 24 => 1, 44 => -1, 74 => -1, 224 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_first_coeffs :
    first_coeffs 100 cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1, -1, 1, 1, -2, 0, 1, 1, 0,
     0, -1, -2, 1, 2, 1, -1, 0, 0, -1, 2, 0, -3, -2, 0, 0, 0, 5, -3, -1,
     3, -2, 2, -2, -2, 2, 0, 3, 1, 0, 0, 2, -1, -4, 0, -4, 0, 3, -1, 3,
     2, 0, -1, -1, 0, 0, 4, -6, 0, 2, 0, 4, -1, -5, -4, -2, 0, -1, 0, 0,
     0, -1, 5, 5, -2, 2, 1, -4, 6, 2, -2, 0, 2, 1, 0, 0, -6, -1, 3, 2] := by
  eta_coeff

end WeightTwoCusps
