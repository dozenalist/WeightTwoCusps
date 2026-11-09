module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(5z) η(6z)^(-2) η(8z)^2 η(10z)^(-2) η(12z)^2 η(15z)^(-1) η(16z)^(-1) η(20z)^2 η(24z)^(-2) η(30z)^2 η(40z)^(-2) η(48z) η(60z)^(-3) η(80z) η(120z)^7 η(240z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(5z) η(6z)^(-2) η(8z)^2 η(10z)^(-2) η(12z)^2 η(15z)^(-1) η(16z)^(-1) η(20z)^2 η(24z)^(-2) η(30z)^2 η(40z)^(-2) η(48z) η(60z)^(-3) η(80z) η(120z)^7 η(240z)^(-3)` at level 240. -/
abbrev cuspForm_240_eta_1m3_2p7_3p1_4m3_5p1_6m2_8p2_10m2_12p2_15m1_16m1_20p2_24m2_30p2_40m2_48p1_60m3_80p1_120p7_240m3 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 4 => 1, 5 => -2, 7 => 2, 9 => -2, 11 => 2, 14 => -1, 15 => -1, 19 => 2, 23 => -2, 29 => 2, 39 => -2, 47 => 1, 59 => -3, 79 => 1, 119 => 7, 239 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m3_2p7_3p1_4m3_5p1_6m2_8p2_10m2_12p2_15m1_16m1_20p2_24m2_30p2_40m2_48p1_60m3_80p1_120p7_240m3_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m3_2p7_3p1_4m3_5p1_6m2_8p2_10m2_12p2_15m1_16m1_20p2_24m2_30p2_40m2_48p1_60m3_80p1_120p7_240m3 =
    [0, 1, 3, 2, 0, 2, 2, 0, 1, 1, -2, -2, 3, 0, -4, 1, 2, -2, -3, 2,
     -1, -4, 2, 2, -2, -3, 0, -4, -4, 0, 1, -2, -5, 2, 2, 0, -2, 0, -2, -4,
     2, 0, -4, -2, 2, 0, 2, 2, -1, -1, 5, 4, 2, 2, 2, 0, 2, 6, -4, -2,
     -2, 4, -2, 0, 2, -2, 2, 2, 6, -2, -2, -4, 1, -2, 4, 0, -4, -4, 2, 6,
     1, -1, -4, 6, 0, 4, -10, -2, -6, -2, -2, -4, -2, -6, 6, 0, 4, -2, 9, -2] := by
  eta_coeff

end WeightTwoCusps
