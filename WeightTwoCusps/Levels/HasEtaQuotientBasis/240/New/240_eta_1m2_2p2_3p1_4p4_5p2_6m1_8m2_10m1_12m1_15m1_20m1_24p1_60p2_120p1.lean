module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-2) η(2z)^2 η(3z) η(4z)^4 η(5z)^2 η(6z)^(-1) η(8z)^(-2) η(10z)^(-1) η(12z)^(-1) η(15z)^(-1) η(20z)^(-1) η(24z) η(60z)^2 η(120z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z) η(4z)^4 η(5z)^2 η(6z)^(-1) η(8z)^(-2) η(10z)^(-1) η(12z)^(-1) η(15z)^(-1) η(20z)^(-1) η(24z) η(60z)^2 η(120z)` at level 240. -/
abbrev cuspForm_240_eta_1m2_2p2_3p1_4p4_5p2_6m1_8m2_10m1_12m1_15m1_20m1_24p1_60p2_120p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -2, 1 => 2, 2 => 1, 3 => 4, 4 => 2, 5 => -1, 7 => -2, 9 => -1, 11 => -1, 14 => -1, 19 => -1, 23 => 1, 59 => 2, 119 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m2_2p2_3p1_4p4_5p2_6m1_8m2_10m1_12m1_15m1_20m1_24p1_60p2_120p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m2_2p2_3p1_4p4_5p2_6m1_8m2_10m1_12m1_15m1_20m1_24p1_60p2_120p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 5, 3, 1, 0, -3, -2, 1, 1,
     -1, 0, -4, -3, 1, 2, 4, -2, 0, -3, -2, 3, 4, -1, -4, -1, -10, -3, -2, -1,
     -1, 1, 3, -1, 2, 0, 1, -1, 2, 1, -2, -2, 2, 0, 3, 1, -2, -3, -2, -3,
     -4, 3, -4, 1, 1, 1, -4, -1, -2, -7, 1, 2, 0, -4, -4, 2, -4, 2, 4, -3,
     -2, -3, 0, -3, 8, -2, 7, 1, 2, 8, 3, 2, 2, 7, 3, 1, -3, 2, -4, 1] := by
  eta_coeff

end WeightTwoCusps
