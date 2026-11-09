module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^3 η(5z)^2 η(6z) η(8z)^(-1) η(10z) η(12z)^(-2) η(15z)^(-1) η(20z)^(-2) η(24z) η(30z)^(-1) η(40z) η(60z)^3 η(120z)^(-1)`; see
[the local level table](../../TABLE.md#level-120).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^3 η(5z)^2 η(6z) η(8z)^(-1) η(10z) η(12z)^(-2) η(15z)^(-1) η(20z)^(-2) η(24z) η(30z)^(-1) η(40z) η(60z)^3 η(120z)^(-1)` at level 120. -/
abbrev cuspForm_120_eta_1m1_2m1_3p2_4p3_5p2_6p1_8m1_10p1_12m2_15m1_20m2_24p1_30m1_40p1_60p3_120m1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -1, 1 => -1, 2 => 2, 3 => 3, 4 => 2, 5 => 1, 7 => -1, 9 => 1, 11 => -2, 14 => -1, 19 => -2, 23 => 1, 29 => -1, 39 => 1, 59 => 3, 119 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m1_2m1_3p2_4p3_5p2_6p1_8m1_10p1_12m2_15m1_20m2_24p1_30m1_40p1_60p3_120m1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m1_2m1_3p2_4p3_5p2_6p1_8m1_10p1_12m2_15m1_20m2_24p1_30m1_40p1_60p3_120m1 =
    [0, 0, 1, 1, 3, 2, 4, 1, 2, -1, 0, -2, -2, -2, -6, -3, -7, 0, -3, 4,
     2, 3, -2, -1, -3, -2, 0, 0, -2, -4, -5, -2, 2, 2, 12, -1, 3, -6, 0, 0,
     3, 6, 2, 1, -10, 3, -4, 5, 8, 2, 1, -6, -4, 2, 0, 6, 2, -4, -12, -4,
     -3, 2, 12, -1, 13, -2, 2, 3, 8, 1, 6, -2, 2, -4, -4, 3, 8, 0, 10, 4,
     -8, 4, -6, 5, -2, 4, 4, 6, -10, 0, 4, -6, 0, -2, 8, -8, -3, 0, 9, -2] := by
  eta_coeff

end WeightTwoCusps
