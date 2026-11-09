module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(5z) η(6z)^(-3) η(10z)^(-3) η(12z)^2 η(15z)^(-2) η(20z)^2 η(30z)^7 η(50z)^2 η(60z)^(-3) η(100z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(5z) η(6z)^(-3) η(10z)^(-3) η(12z)^2 η(15z)^(-2) η(20z)^2 η(30z)^7 η(50z)^2 η(60z)^(-3) η(100z)^(-1)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p5_3p1_4m2_5p1_6m3_10m3_12p2_15m2_20p2_30p7_50p2_60m3_100m1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 4 => 1, 5 => -3, 9 => -3, 11 => 2, 14 => -2, 19 => 2, 29 => 7, 49 => 2, 59 => -3, 99 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p5_3p1_4m2_5p1_6m3_10m3_12p2_15m2_20p2_30p7_50p2_60m3_100m1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p5_3p1_4m2_5p1_6m3_10m3_12p2_15m2_20p2_30p7_50p2_60m3_100m1 =
    [0, 1, 2, 0, -1, 0, -1, 0, 2, 1, -1, 0, 2, 0, 0, 1, -1, 0, 2, 2,
     2, 0, 0, 0, -1, 1, 0, 0, 0, 0, 2, 0, -2, 0, 0, 0, 1, 0, 0, -2,
     1, 0, -4, 0, 0, -2, 0, 0, -2, -3, -2, 0, -4, 0, 3, -2, 2, 0, -4, -2,
     -3, -2, -4, 0, 3, -2, 4, 0, -8, -2, -2, 0, 2, 0, 2, -2, 2, 0, -4, 0,
     -6, -3, 4, 0, 2, 2, -2, 0, 0, 4, -1, -4, 4, 0, 0, 4, -1, 0, -2, 2] := by
  eta_coeff

end WeightTwoCusps
