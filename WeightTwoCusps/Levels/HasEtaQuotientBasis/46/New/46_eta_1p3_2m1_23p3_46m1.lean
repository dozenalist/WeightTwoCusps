module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 46

The eta expression is `η(z)^3 η(2z)^(-1) η(23z)^3 η(46z)^(-1)`; see
[the local level table](../../TABLE.md#level-46).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-1) η(23z)^3 η(46z)^(-1)` at level 46. -/
abbrev cuspForm_46_eta_1p3_2m1_23p3_46m1 : gamma0CuspForms 46 :=
  etaQuotientCuspForm 46 sparse![46; 0 => 3, 1 => -1, 22 => 3, 45 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_46_eta_1p3_2m1_23p3_46m1_first_coeffs :
    first_coeffs 100 cuspForm_46_eta_1p3_2m1_23p3_46m1 =
    [0, 1, -3, 1, 2, 2, -1, -4, 1, -2, 0, 2, 4, -1, 2, -2, -1, 0, -2, -2,
     -2, 0, 4, 1, -3, 11, -5, -1, -6, 1, 12, -3, 2, -2, -6, -12, 0, -2, 6, 3,
     -2, 7, 10, 8, 2, -12, -3, 1, -11, 5, -13, 4, 2, -6, 1, 8, 8, -2, 5, 8,
     -10, -2, 3, 8, -5, -10, -8, -10, 6, 1, 4, 1, 6, 9, 0, 3, -4, -4, -3, -6,
     16, 5, -9, 8, -2, -12, -8, -3, -10, -4, 16, 4, 2, -3, -1, -4, 16, 4, -3, -4] := by
  eta_coeff

end WeightTwoCusps
