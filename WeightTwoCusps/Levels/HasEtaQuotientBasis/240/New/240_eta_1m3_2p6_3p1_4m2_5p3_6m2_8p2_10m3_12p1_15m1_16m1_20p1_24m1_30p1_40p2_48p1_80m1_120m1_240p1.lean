module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-2) η(5z)^3 η(6z)^(-2) η(8z)^2 η(10z)^(-3) η(12z) η(15z)^(-1) η(16z)^(-1) η(20z) η(24z)^(-1) η(30z) η(40z)^2 η(48z) η(80z)^(-1) η(120z)^(-1) η(240z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-2) η(5z)^3 η(6z)^(-2) η(8z)^2 η(10z)^(-3) η(12z) η(15z)^(-1) η(16z)^(-1) η(20z) η(24z)^(-1) η(30z) η(40z)^2 η(48z) η(80z)^(-1) η(120z)^(-1) η(240z)` at level 240. -/
abbrev cuspForm_240_eta_1m3_2p6_3p1_4m2_5p3_6m2_8p2_10m3_12p1_15m1_16m1_20p1_24m1_30p1_40p2_48p1_80m1_120m1_240p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -3, 1 => 6, 2 => 1, 3 => -2, 4 => 3, 5 => -2, 7 => 2, 9 => -3, 11 => 1, 14 => -1, 15 => -1, 19 => 1, 23 => -1, 29 => 1, 39 => 2, 47 => 1, 79 => -1, 119 => -1, 239 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m3_2p6_3p1_4m2_5p3_6m2_8p2_10m3_12p1_15m1_16m1_20p1_24m1_30p1_40p2_48p1_80m1_120m1_240p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m3_2p6_3p1_4m2_5p3_6m2_8p2_10m3_12p1_15m1_16m1_20p1_24m1_30p1_40p2_48p1_80m1_120m1_240p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 3, 3, 3, 5, 3, 0, 3, 3, -3, 0, 3, -4,
     0, 9, 3, -4, 3, 0, -9, 0, 6, 0, -3, 8, 3, -6, 3, 1, -12, -12, 6, -3,
     -3, 12, 6, -4, 0, 3, -18, -10, -3, -12, -9, 3, 0, -12, -6, -7, -12, -12, -3, 1,
     -3, 0, 6, -3, -3, 0, -3, -14, -12, -9, -3, 6, 3, 12, -3, -3, 0, 12, -3, 0,
     3, -6, 0, -2, 12, 0, 12, -3, 0, 0, 0, -2, 6, 18, 12, 8, 3, 12, 0, 9] := by
  eta_coeff

end WeightTwoCusps
