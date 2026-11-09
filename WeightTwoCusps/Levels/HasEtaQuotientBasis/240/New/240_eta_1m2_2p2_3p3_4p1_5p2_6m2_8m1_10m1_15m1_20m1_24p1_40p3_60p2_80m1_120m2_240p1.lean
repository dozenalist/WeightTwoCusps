module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^3 η(4z) η(5z)^2 η(6z)^(-2) η(8z)^(-1) η(10z)^(-1) η(15z)^(-1) η(20z)^(-1) η(24z) η(40z)^3 η(60z)^2 η(80z)^(-1) η(120z)^(-2) η(240z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^3 η(4z) η(5z)^2 η(6z)^(-2) η(8z)^(-1) η(10z)^(-1) η(15z)^(-1) η(20z)^(-1) η(24z) η(40z)^3 η(60z)^2 η(80z)^(-1) η(120z)^(-2) η(240z)` at level 240. -/
abbrev cuspForm_240_eta_1m2_2p2_3p3_4p1_5p2_6m2_8m1_10m1_15m1_20m1_24p1_40p3_60p2_80m1_120m2_240p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -2, 1 => 2, 2 => 3, 3 => 1, 4 => 2, 5 => -2, 7 => -1, 9 => -1, 14 => -1, 19 => -1, 23 => 1, 39 => 3, 59 => 2, 79 => -1, 119 => -2, 239 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m2_2p2_3p3_4p1_5p2_6m2_8m1_10m1_15m1_20m1_24p1_40p3_60p2_80m1_120m2_240p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m2_2p2_3p3_4p1_5p2_6m2_8m1_10m1_15m1_20m1_24p1_40p3_60p2_80m1_120m2_240p1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 3, 3, 2, 1, -1, 0, 1, 2, 1, 0, -2, -3,
     0, 2, 4, 0, 1, -1, -2, 2, 4, 3, 0, -1, -3, -4, -4, 0, -2, -2, 2, 1,
     -1, 3, 0, 2, 0, -1, -1, -6, -5, -7, -4, -4, 0, -6, -2, -6, -8, 0, 2, 5,
     1, -1, -8, -4, -3, -1, 0, -6, -8, -9, -5, 4, 3, 8, 6, -3, 0, 4, -4, -5,
     5, -7, -4, -8, 2, 1, -3, 4, -4, -4, 0, 4, 4, 12, 1, 3, 7, 4, 4, 5] := by
  eta_coeff

end WeightTwoCusps
