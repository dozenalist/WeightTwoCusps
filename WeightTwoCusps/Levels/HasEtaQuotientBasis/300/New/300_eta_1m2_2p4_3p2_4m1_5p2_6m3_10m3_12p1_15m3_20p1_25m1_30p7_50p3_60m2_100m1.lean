module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(5z)^2 η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-3) η(20z) η(25z)^(-1) η(30z)^7 η(50z)^3 η(60z)^(-2) η(100z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(5z)^2 η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-3) η(20z) η(25z)^(-1) η(30z)^7 η(50z)^3 η(60z)^(-2) η(100z)^(-1)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p4_3p2_4m1_5p2_6m3_10m3_12p1_15m3_20p1_25m1_30p7_50p3_60m2_100m1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 4 => 2, 5 => -3, 9 => -3, 11 => 1, 14 => -3, 19 => 1, 24 => -1, 29 => 7, 49 => 3, 59 => -2, 99 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p4_3p2_4m1_5p2_6m3_10m3_12p1_15m3_20p1_25m1_30p7_50p3_60m2_100m1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p4_3p2_4m1_5p2_6m3_10m3_12p1_15m3_20p1_25m1_30p7_50p3_60m2_100m1 =
    [0, 0, 0, 1, 2, 1, 0, -1, -2, -2, 0, 2, 0, -1, 0, 0, 0, 3, 3, -2,
     -3, 0, 1, 0, 2, 0, -4, -3, 2, 2, -1, -2, -2, -3, -2, 4, 2, 0, -3, 0,
     2, 0, 2, 1, -4, -5, 2, 2, 0, 0, 1, -4, -2, 2, 0, -2, 0, 2, 2, 4,
     4, 0, -2, 1, -2, 0, 2, -4, -3, 4, 2, 2, 1, 1, -4, -1, 4, 0, -2, 4,
     5, 2, 3, 1, -2, -8, 4, 0, 1, 2, 0, 2, 2, 3, 6, 0, -4, 1, 0, 2] := by
  eta_coeff

end WeightTwoCusps
