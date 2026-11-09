module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^3 η(4z) η(5z) η(6z)^(-2) η(8z)^(-1) η(10z) η(20z)^(-1) η(24z) η(30z)^(-1) η(40z) η(60z)^2 η(120z)^(-1)`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^3 η(4z) η(5z) η(6z)^(-2) η(8z)^(-1) η(10z) η(20z)^(-1) η(24z) η(30z)^(-1) η(40z) η(60z)^2 η(120z)^(-1)` at level 240. -/
abbrev cuspForm_240_eta_1m2_2p2_3p3_4p1_5p1_6m2_8m1_10p1_20m1_24p1_30m1_40p1_60p2_120m1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -2, 1 => 2, 2 => 3, 3 => 1, 4 => 1, 5 => -2, 7 => -1, 9 => 1, 19 => -1, 23 => 1, 29 => -1, 39 => 1, 59 => 2, 119 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m2_2p2_3p3_4p1_5p1_6m2_8m1_10p1_20m1_24p1_30m1_40p1_60p2_120m1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m2_2p2_3p3_4p1_5p1_6m2_8m1_10p1_20m1_24p1_30m1_40p1_60p2_120m1 =
    [0, 1, 2, 3, 3, 2, 2, 1, 3, 4, 4, 2, -1, -2, -2, 2, 3, 4, -2, -2,
     -1, -1, 4, 1, 1, -3, -4, 0, 0, -2, -2, -4, -5, 0, 0, -1, -1, -6, 4, 0,
     -1, 6, -4, -1, -4, -1, -2, -5, -7, -3, -6, -8, 2, -10, -4, -4, -8, 0, -4, 4,
     -1, -6, -8, -5, -5, -6, 4, -7, -2, -11, -6, 6, 3, 10, 4, -1, -4, 0, -4, -2,
     7, -5, -4, -13, -4, 4, -6, 8, -4, -2, 0, 2, 8, 14, 10, 2, 9, 2, 10, 2] := by
  eta_coeff

end WeightTwoCusps
