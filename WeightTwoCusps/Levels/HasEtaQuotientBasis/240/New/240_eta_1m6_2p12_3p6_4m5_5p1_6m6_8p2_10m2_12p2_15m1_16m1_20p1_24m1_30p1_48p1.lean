module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-6) η(2z)^12 η(3z)^6 η(4z)^(-5) η(5z) η(6z)^(-6) η(8z)^2 η(10z)^(-2) η(12z)^2 η(15z)^(-1) η(16z)^(-1) η(20z) η(24z)^(-1) η(30z) η(48z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-6) η(2z)^12 η(3z)^6 η(4z)^(-5) η(5z) η(6z)^(-6) η(8z)^2 η(10z)^(-2) η(12z)^2 η(15z)^(-1) η(16z)^(-1) η(20z) η(24z)^(-1) η(30z) η(48z)` at level 240. -/
abbrev cuspForm_240_eta_1m6_2p12_3p6_4m5_5p1_6m6_8p2_10m2_12p2_15m1_16m1_20p1_24m1_30p1_48p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -6, 1 => 12, 2 => 6, 3 => -5, 4 => 1, 5 => -6, 7 => 2, 9 => -2, 11 => 2, 14 => -1, 15 => -1, 19 => 1, 23 => -1, 29 => 1, 47 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m6_2p12_3p6_4m5_5p1_6m6_8p2_10m2_12p2_15m1_16m1_20p1_24m1_30p1_48p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m6_2p12_3p6_4m5_5p1_6m6_8p2_10m2_12p2_15m1_16m1_20p1_24m1_30p1_48p1 =
    [0, 0, 1, 6, 15, 20, 14, 5, 10, 25, 28, 16, 0, -10, -10, 8, 35, 20, -19, -26,
     0, 25, 14, 13, -5, -40, -12, 21, 30, -10, -23, -8, -50, -20, 12, -5, -45, -50, 16, -2,
     5, 30, -10, -39, -30, 15, -8, -45, -40, -50, -51, -8, 0, -40, -26, -12, -10, -30, -4, 46,
     -15, -10, -12, -25, -25, -30, 26, -41, -60, -35, -10, 2, 10, 60, 16, -6, 0, 40, 2, 18,
     40, -20, -26, -31, 30, 20, 4, 6, -30, 0, 28, 10, 60, 60, 20, 22, 55, 40, 13, 16] := by
  eta_coeff

end WeightTwoCusps
