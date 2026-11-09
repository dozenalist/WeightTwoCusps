module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(5z)^(-1) η(6z)^(-2) η(10z)^3 η(12z) η(15z)^(-1) η(20z)^(-1) η(25z) η(30z)^3 η(50z)^(-2) η(60z)^(-1) η(75z)^(-2) η(100z) η(150z)^5 η(300z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(5z)^(-1) η(6z)^(-2) η(10z)^3 η(12z) η(15z)^(-1) η(20z)^(-1) η(25z) η(30z)^3 η(50z)^(-2) η(60z)^(-1) η(75z)^(-2) η(100z) η(150z)^5 η(300z)^(-2)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p5_3p1_4m2_5m1_6m2_10p3_12p1_15m1_20m1_25p1_30p3_50m2_60m1_75m2_100p1_150p5_300m2 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 4 => -1, 5 => -2, 9 => 3, 11 => 1, 14 => -1, 19 => -1, 24 => 1, 29 => 3, 49 => -2, 59 => -1, 74 => -2, 99 => 1, 149 => 5, 299 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p5_3p1_4m2_5m1_6m2_10p3_12p1_15m1_20m1_25p1_30p3_50m2_60m1_75m2_100p1_150p5_300m2_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p5_3p1_4m2_5m1_6m2_10p3_12p1_15m1_20m1_25p1_30p3_50m2_60m1_75m2_100p1_150p5_300m2 =
    [0, 0, 1, 2, 0, -1, 0, 1, 3, 0, -1, 0, -3, -1, 0, 1, 0, -2, 1, 0,
     -1, 0, 2, 2, 0, -1, 0, -4, -6, 0, 1, 0, -5, -6, 0, 0, 0, 4, -4, 0,
     3, 0, 6, -3, 0, -1, 0, 2, -1, 0, -1, 0, 4, 6, 0, 4, 0, 9, 10, 0,
     1, 0, -2, 1, 0, 2, 0, -9, 4, 0, 0, 0, 3, 2, 0, 1, 0, -2, -8, 0,
     -1, 0, -12, -8, 0, -2, 0, 0, -2, 0, -1, 0, 8, 3, 0, -4, 0, -1, 3, 0] := by
  eta_coeff

end WeightTwoCusps
