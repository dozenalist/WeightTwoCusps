module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-5) η(2z)^9 η(3z)^5 η(4z)^(-1) η(5z) η(6z)^(-6) η(8z)^(-1) η(10z)^(-2) η(12z)^4 η(15z)^(-1) η(20z) η(24z)^(-1) η(30z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-5) η(2z)^9 η(3z)^5 η(4z)^(-1) η(5z) η(6z)^(-6) η(8z)^(-1) η(10z)^(-2) η(12z)^4 η(15z)^(-1) η(20z) η(24z)^(-1) η(30z)` at level 240. -/
abbrev cuspForm_240_eta_1m5_2p9_3p5_4m1_5p1_6m6_8m1_10m2_12p4_15m1_20p1_24m1_30p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -5, 1 => 9, 2 => 5, 3 => -1, 4 => 1, 5 => -6, 7 => -1, 9 => -2, 11 => 4, 14 => -1, 19 => 1, 23 => -1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m5_2p9_3p5_4m1_5p1_6m6_8m1_10m2_12p4_15m1_20p1_24m1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m5_2p9_3p5_4m1_5p1_6m6_8m1_10m2_12p4_15m1_20p1_24m1_30p1 =
    [0, 1, 5, 11, 15, 13, 5, 0, 5, 21, 35, 26, 5, -12, -10, 13, 25, 22, -5, -26,
     -5, 10, 20, 18, -5, -11, -10, 11, 20, -24, -25, -18, -35, 6, 10, -10, -45, -64, 0, -12,
     5, 44, -30, -54, -20, 3, -10, -50, -25, -37, -75, 2, 10, -42, -25, -2, 0, -26, 10, 46,
     -15, -12, 0, -10, -15, -16, 20, -46, -50, -32, -10, 12, 5, 50, 30, -1, -20, 20, -10, 18,
     25, -9, -30, -66, 20, 6, -10, -4, -20, -6, 25, 20, 60, 42, 10, 22, 35, 22, 5, 6] := by
  eta_coeff

end WeightTwoCusps
