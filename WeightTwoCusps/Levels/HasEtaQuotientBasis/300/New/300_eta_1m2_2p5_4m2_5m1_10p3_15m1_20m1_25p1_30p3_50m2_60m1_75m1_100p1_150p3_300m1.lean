module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(5z)^(-1) η(10z)^3 η(15z)^(-1) η(20z)^(-1) η(25z) η(30z)^3 η(50z)^(-2) η(60z)^(-1) η(75z)^(-1) η(100z) η(150z)^3 η(300z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(5z)^(-1) η(10z)^3 η(15z)^(-1) η(20z)^(-1) η(25z) η(30z)^3 η(50z)^(-2) η(60z)^(-1) η(75z)^(-1) η(100z) η(150z)^3 η(300z)^(-1)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p5_4m2_5m1_10p3_15m1_20m1_25p1_30p3_50m2_60m1_75m1_100p1_150p3_300m1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 5, 3 => -2, 4 => -1, 9 => 3, 14 => -1, 19 => -1, 24 => 1, 29 => 3, 49 => -2, 59 => -1, 74 => -1, 99 => 1, 149 => 3, 299 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p5_4m2_5m1_10p3_15m1_20m1_25p1_30p3_50m2_60m1_75m1_100p1_150p3_300m1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p5_4m2_5m1_10p3_15m1_20m1_25p1_30p3_50m2_60m1_75m1_100p1_150p3_300m1 =
    [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 1, 2, 0, 0, 4, -1, -2, 0, 0, 0,
     1, 4, 0, 0, 0, 1, 4, 0, 0, 4, -1, -8, 0, 0, -4, 0, -2, 0, 0, -10,
     -3, 2, 0, 0, -6, 1, -6, 0, 0, -4, 1, -8, 0, 0, -2, -4, 4, 0, 0, 4,
     -1, 6, 0, 0, 8, -2, -8, 0, 0, 10, 0, 4, 0, 0, 8, -1, 6, 0, 0, -2,
     1, -8, 0, 0, -6, 2, -4, 0, 0, -14, 1, 10, 0, 0, -14, 4, -2, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
