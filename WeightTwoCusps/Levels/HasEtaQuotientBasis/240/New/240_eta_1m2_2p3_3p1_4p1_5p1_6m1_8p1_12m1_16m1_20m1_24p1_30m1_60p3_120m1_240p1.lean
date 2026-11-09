module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(4z) η(5z) η(6z)^(-1) η(8z) η(12z)^(-1) η(16z)^(-1) η(20z)^(-1) η(24z) η(30z)^(-1) η(60z)^3 η(120z)^(-1) η(240z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(4z) η(5z) η(6z)^(-1) η(8z) η(12z)^(-1) η(16z)^(-1) η(20z)^(-1) η(24z) η(30z)^(-1) η(60z)^3 η(120z)^(-1) η(240z)` at level 240. -/
abbrev cuspForm_240_eta_1m2_2p3_3p1_4p1_5p1_6m1_8p1_12m1_16m1_20m1_24p1_30m1_60p3_120m1_240p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -2, 1 => 3, 2 => 1, 3 => 1, 4 => 1, 5 => -1, 7 => 1, 11 => -1, 15 => -1, 19 => -1, 23 => 1, 29 => -1, 59 => 3, 119 => -1, 239 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m2_2p3_3p1_4p1_5p1_6m1_8p1_12m1_16m1_20m1_24p1_30m1_60p3_120m1_240p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m2_2p3_3p1_4p1_5p1_6m1_8p1_12m1_16m1_20m1_24p1_30m1_60p3_120m1_240p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3, 2, 1, 2, 2, 1,
     -1, -1, -4, -2, 1, 1, 2, -2, 0, -3, 1, 3, 0, -2, -6, 0, -4, 4, 0, -3,
     -1, -7, 0, -2, 2, -2, 1, 0, -2, 7, 2, 4, 2, 2, 1, -6, -2, -2, -2, -3,
     -1, -3, -6, 2, -3, -1, 0, -2, -2, -4, -1, 0, 0, -4, -6, -3, -4, -4, -2, 3,
     2, 1, 6, 4, 2, -3, 3, -4, 2, 8, 0, -4, 2, 8, 3, 7, 1, -4, -2, 1] := by
  eta_coeff

end WeightTwoCusps
