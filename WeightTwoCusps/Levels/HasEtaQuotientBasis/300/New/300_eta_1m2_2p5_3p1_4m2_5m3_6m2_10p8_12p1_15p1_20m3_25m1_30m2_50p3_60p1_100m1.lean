module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(5z)^(-3) η(6z)^(-2) η(10z)^8 η(12z) η(15z) η(20z)^(-3) η(25z)^(-1) η(30z)^(-2) η(50z)^3 η(60z) η(100z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(5z)^(-3) η(6z)^(-2) η(10z)^8 η(12z) η(15z) η(20z)^(-3) η(25z)^(-1) η(30z)^(-2) η(50z)^3 η(60z) η(100z)^(-1)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p5_3p1_4m2_5m3_6m2_10p8_12p1_15p1_20m3_25m1_30m2_50p3_60p1_100m1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 4 => -3, 5 => -2, 9 => 8, 11 => 1, 14 => 1, 19 => -3, 24 => -1, 29 => -2, 49 => 3, 59 => 1, 99 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p5_3p1_4m2_5m3_6m2_10p8_12p1_15p1_20m3_25m1_30m2_50p3_60p1_100m1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p5_3p1_4m2_5m3_6m2_10p8_12p1_15p1_20m3_25m1_30m2_50p3_60p1_100m1 =
    [0, 0, 1, 2, 0, -1, 0, 3, 7, 0, -3, 0, -1, 5, 0, -1, 0, -10, -5, 0,
     3, 0, -6, -6, 0, 1, 0, 6, -2, 0, -3, 0, 7, 4, 0, -8, 0, 0, 8, 0,
     -3, 0, -10, -5, 0, 11, 0, -6, -7, 0, 3, 0, 4, -10, 0, 0, 0, 1, -18, 0,
     3, 0, 14, -1, 0, -2, 0, 17, 0, 0, 12, 0, 1, 6, 0, 1, 0, 2, 8, 0,
     3, 0, 0, -4, 0, 18, 0, 8, 6, 0, -3, 0, 0, -7, 0, 4, 0, -15, 3, 0] := by
  eta_coeff

end WeightTwoCusps
