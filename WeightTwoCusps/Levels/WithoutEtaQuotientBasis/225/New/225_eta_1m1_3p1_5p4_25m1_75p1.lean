module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 225

The eta expression is `η(z)^(-1) η(3z) η(5z)^4 η(25z)^(-1) η(75z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(5z)^4 η(25z)^(-1) η(75z)` at level 225. -/
abbrev cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1 : gamma0CuspForms 225 :=
  etaQuotientCuspForm 225 sparse![225; 0 => -1, 2 => 1, 4 => 4, 24 => -1, 74 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_first_coeffs :
    first_coeffs 100 cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1 =
    [0, 0, 0, 1, 1, 2, 2, 4, 1, 3, 1, 5, 0, 4, 1, 4, -4, 1, 0, 3,
     -2, 1, -1, 1, -8, -1, -3, 1, -7, 1, -4, 5, -3, -2, -1, 0, -2, -6, -3, 5,
     -3, -12, -2, 3, -6, -4, 1, 3, -2, -18, -2, -6, -8, -4, 2, 4, 0, 1, -2, 7,
     -4, 9, -1, 1, 10, -4, -12, 2, 0, -2, 0, 12, -2, -8, -14, 4, -5, -1, 2, 3,
     -2, 3, 3, 5, 2, -2, 5, 2, 2, 8, 4, -19, 2, -1, -5, 8, 16, 2, 3, -10] := by
  eta_coeff

end WeightTwoCusps
