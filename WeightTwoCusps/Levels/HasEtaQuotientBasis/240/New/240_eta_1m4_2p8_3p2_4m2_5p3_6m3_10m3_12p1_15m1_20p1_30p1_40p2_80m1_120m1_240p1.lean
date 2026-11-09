module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-4) η(2z)^8 η(3z)^2 η(4z)^(-2) η(5z)^3 η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-1) η(20z) η(30z) η(40z)^2 η(80z)^(-1) η(120z)^(-1) η(240z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^2 η(4z)^(-2) η(5z)^3 η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-1) η(20z) η(30z) η(40z)^2 η(80z)^(-1) η(120z)^(-1) η(240z)` at level 240. -/
abbrev cuspForm_240_eta_1m4_2p8_3p2_4m2_5p3_6m3_10m3_12p1_15m1_20p1_30p1_40p2_80m1_120m1_240p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -4, 1 => 8, 2 => 2, 3 => -2, 4 => 3, 5 => -3, 9 => -3, 11 => 1, 14 => -1, 19 => 1, 29 => 1, 39 => 2, 79 => -1, 119 => -1, 239 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m4_2p8_3p2_4m2_5p3_6m3_10m3_12p1_15m1_20p1_30p1_40p2_80m1_120m1_240p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m4_2p8_3p2_4m2_5p3_6m3_10m3_12p1_15m1_20p1_30p1_40p2_80m1_120m1_240p1 =
    [0, 0, 0, 0, 0, 0, 1, 4, 6, 6, 7, 5, 0, 0, 3, 3, 3, 6, 4, -1,
     3, 9, 2, -4, 3, -3, -8, 6, 12, 3, -1, 5, -6, -12, -2, -2, -12, -6, 10, -3,
     -3, 3, -4, -10, -6, 0, -13, -10, -12, -15, -12, -6, -6, -18, -14, -16, -18, -12, -4, 1,
     -3, -9, -8, -6, -9, -3, 6, -14, -18, -12, -7, 0, 6, 24, -4, -9, 12, 12, -10, 9,
     12, -9, 0, 4, 18, -3, 13, 6, -6, 0, -1, -8, 6, 30, 17, 17, 15, 12, 0, 9] := by
  eta_coeff

end WeightTwoCusps
