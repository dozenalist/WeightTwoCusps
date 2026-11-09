module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-1) η(2z)^(-2) η(3z)^2 η(4z)^6 η(5z)^2 η(8z)^(-2) η(10z)^(-1) η(12z)^(-1) η(15z)^(-1) η(30z) η(60z)^(-1) η(120z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-2) η(3z)^2 η(4z)^6 η(5z)^2 η(8z)^(-2) η(10z)^(-1) η(12z)^(-1) η(15z)^(-1) η(30z) η(60z)^(-1) η(120z)^2` at level 240. -/
abbrev cuspForm_240_eta_1m1_2m2_3p2_4p6_5p2_8m2_10m1_12m1_15m1_30p1_60m1_120p2 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -1, 1 => -2, 2 => 2, 3 => 6, 4 => 2, 7 => -2, 9 => -1, 11 => -1, 14 => -1, 29 => 1, 59 => -1, 119 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m1_2m2_3p2_4p6_5p2_8m2_10m1_12m1_15m1_30p1_60m1_120p2_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m1_2m2_3p2_4p6_5p2_8m2_10m1_12m1_15m1_30p1_60m1_120p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 3, 6, 2, 4, -1, 2, -1, 3, 0,
     1, 0, -2, 0, 0, 2, 0, 1, -2, -1, -5, 2, -3, 0, -2, -1, -10, -4, -4, -3,
     0, 0, 1, -8, -2, 0, -8, -4, -3, -6, -12, 3, -2, -1, 0, 6, -2, -3, 2, -1,
     -7, 4, 8, 1, -2, 3, -2, -4, 6, 1, 2, -2, 1, 2, -4, 2, 4, 2, 0, 6,
     3, 0, 4, 2, 12, -4, 8, -2, -2, 2, 7, -2, -4, -3, 0, -2, 4, 2, -8, 1] := by
  eta_coeff

end WeightTwoCusps
