module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z)^2 η(6z)^(-3) η(10z)^(-2) η(12z)^3 η(15z)^(-1) η(24z)^(-1) η(30z)^2 η(40z)^2 η(60z)^(-1) η(80z)^(-1) η(240z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z)^2 η(6z)^(-3) η(10z)^(-2) η(12z)^3 η(15z)^(-1) η(24z)^(-1) η(30z)^2 η(40z)^2 η(60z)^(-1) η(80z)^(-1) η(240z)` at level 240. -/
abbrev cuspForm_240_eta_1m3_2p6_3p2_4m2_5p2_6m3_10m2_12p3_15m1_24m1_30p2_40p2_60m1_80m1_240p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 2, 5 => -3, 9 => -2, 11 => 3, 14 => -1, 23 => -1, 29 => 2, 39 => 2, 59 => -1, 79 => -1, 239 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m3_2p6_3p2_4m2_5p2_6m3_10m2_12p3_15m1_24m1_30p2_40p2_60m1_80m1_240p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m3_2p6_3p2_4m2_5p2_6m3_10m2_12p3_15m1_24m1_30p2_40p2_60m1_80m1_240p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 3, 2, 2, 1, 0, 1, 4, 4, 1,
     1, 0, -4, -2, 3, -1, -2, 2, 2, -1, 0, 7, 2, -2, 2, 0, -6, 0, 4, -3,
     -3, -5, -6, -10, -2, 1, -5, -4, -4, -3, -4, 2, -2, -6, -9, -4, -6, -6, -2, -5,
     -3, -5, 2, -2, -7, -1, 8, -6, -2, 5, 1, -4, 0, 8, -10, -3, 4, 4, -2, 11,
     4, 1, 6, 12, 8, -5, 13, 0, 6, 8, 1, -8, 0, 2, 9, 9, 1, 4, -10, 3] := by
  eta_coeff

end WeightTwoCusps
