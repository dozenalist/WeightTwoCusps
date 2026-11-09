module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-3) η(2z)^5 η(3z)^3 η(5z) η(6z)^(-3) η(8z)^(-1) η(15z)^(-1) η(20z)^(-1) η(24z) η(30z)^2 η(40z) η(60z) η(120z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^3 η(5z) η(6z)^(-3) η(8z)^(-1) η(15z)^(-1) η(20z)^(-1) η(24z) η(30z)^2 η(40z) η(60z) η(120z)^(-1)` at level 240. -/
abbrev cuspForm_240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -3, 1 => 5, 2 => 3, 4 => 1, 5 => -3, 7 => -1, 14 => -1, 19 => -1, 23 => 1, 29 => 2, 39 => 1, 59 => 1, 119 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1 =
    [0, 1, 3, 4, 4, 2, 0, 0, 1, 5, 4, 0, -3, -6, -2, 3, 8, 6, -1, -4,
     -1, 4, 6, 8, -2, -5, -4, 0, 6, -2, -3, -8, -11, -4, 0, 0, -4, -6, 0, 0,
     2, 6, 2, -4, -6, -2, -8, -8, -7, -3, -9, -4, 2, -6, 0, -4, 2, 0, 0, 8,
     0, -6, -4, -8, -4, -4, -6, -4, -14, -12, -6, 0, 1, 10, 8, -2, -4, 0, 2, 0,
     7, -3, -10, -12, -2, 4, 0, 8, -6, -6, 0, 8, 16, 16, 12, 4, 10, 2, 3, 0] := by
  eta_coeff

end WeightTwoCusps
