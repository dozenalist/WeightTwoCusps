module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-3) η(2z)^5 η(3z)^3 η(5z)^2 η(6z)^(-3) η(8z)^(-1) η(10z)^(-2) η(15z)^(-2) η(20z)^(-1) η(24z) η(30z)^3 η(40z)^3 η(60z) η(80z)^(-1) η(120z)^(-2) η(240z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^3 η(5z)^2 η(6z)^(-3) η(8z)^(-1) η(10z)^(-2) η(15z)^(-2) η(20z)^(-1) η(24z) η(30z)^3 η(40z)^3 η(60z) η(80z)^(-1) η(120z)^(-2) η(240z)` at level 240. -/
abbrev cuspForm_240_eta_1m3_2p5_3p3_5p2_6m3_8m1_10m2_15m2_20m1_24p1_30p3_40p3_60p1_80m1_120m2_240p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -3, 1 => 5, 2 => 3, 4 => 2, 5 => -3, 7 => -1, 9 => -2, 14 => -2, 19 => -1, 23 => 1, 29 => 3, 39 => 3, 59 => 1, 79 => -1, 119 => -2, 239 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m3_2p5_3p3_5p2_6m3_8m1_10m2_15m2_20m1_24p1_30p3_40p3_60p1_80m1_120m2_240p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m3_2p5_3p3_5p2_6m3_8m1_10m2_15m2_20m1_24p1_30p3_40p3_60p1_80m1_120m2_240p1 =
    [0, 0, 0, 0, 0, 0, 1, 3, 4, 4, 2, -1, -3, -3, 1, 2, 1, 0, -3, -3,
     1, 7, 6, 2, -1, -2, -2, 3, 10, 3, -1, -3, -6, -7, -4, 0, -4, -5, 0, 1,
     1, 7, 5, 2, -2, -1, -5, -6, -4, -9, -6, -4, -2, -4, 0, -7, -6, -1, 4, 7,
     2, 1, -6, -6, 1, 1, -6, -4, -18, -12, -5, 0, 4, 8, 10, -4, 4, 6, 0, -3,
     4, -7, -10, -4, 6, 2, 1, 5, -10, -8, 1, 4, 8, 15, 1, 3, 9, 6, 2, 5] := by
  eta_coeff

end WeightTwoCusps
