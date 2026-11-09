module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(5z)^3 η(6z)^(-2) η(10z)^(-4) η(12z) η(15z)^(-1) η(20z)^3 η(25z)^(-3) η(30z)^2 η(50z)^7 η(60z)^(-1) η(75z) η(100z)^(-3) η(150z)^(-2) η(300z)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(5z)^3 η(6z)^(-2) η(10z)^(-4) η(12z) η(15z)^(-1) η(20z)^3 η(25z)^(-3) η(30z)^2 η(50z)^7 η(60z)^(-1) η(75z) η(100z)^(-3) η(150z)^(-2) η(300z)` at level 300. -/
abbrev cuspForm_300_eta_1m3_2p7_3p1_4m3_5p3_6m2_10m4_12p1_15m1_20p3_25m3_30p2_50p7_60m1_75p1_100m3_150m2_300p1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 4 => 3, 5 => -2, 9 => -4, 11 => 1, 14 => -1, 19 => 3, 24 => -3, 29 => 2, 49 => 7, 59 => -1, 74 => 1, 99 => -3, 149 => -2, 299 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m3_2p7_3p1_4m3_5p3_6m2_10m4_12p1_15m1_20p3_25m3_30p2_50p7_60m1_75p1_100m3_150m2_300p1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m3_2p7_3p1_4m3_5p3_6m2_10m4_12p1_15m1_20p3_25m3_30p2_50p7_60m1_75p1_100m3_150m2_300p1 =
    [0, 0, 0, 1, 3, 2, 0, 2, 0, -6, -3, 3, 0, -1, 6, 5, -3, -3, 0, -6,
     -6, 3, 0, 0, 6, 1, -6, -2, 3, 0, 0, 3, 6, -3, -9, -2, 3, 2, -3, 9,
     9, -9, -9, -1, -9, -10, 6, 0, 0, 9, 0, -12, -6, 6, -9, -6, 12, 5, -9, 0,
     9, -3, 6, 2, -3, -2, -6, -4, -3, 12, 6, 0, 0, 2, -6, -8, 3, 0, 12, 6,
     6, 15, 3, -9, -12, 6, 6, 3, 12, 9, -3, -3, 6, -1, 12, 4, -6, -4, 6, 3] := by
  eta_coeff

end WeightTwoCusps
