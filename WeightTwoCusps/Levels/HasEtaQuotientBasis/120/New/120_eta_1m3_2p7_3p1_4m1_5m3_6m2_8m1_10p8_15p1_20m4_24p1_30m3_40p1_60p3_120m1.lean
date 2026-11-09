module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-1) η(5z)^(-3) η(6z)^(-2) η(8z)^(-1) η(10z)^8 η(15z) η(20z)^(-4) η(24z) η(30z)^(-3) η(40z) η(60z)^3 η(120z)^(-1)`; see
[the local level table](../../TABLE.md#level-120).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-1) η(5z)^(-3) η(6z)^(-2) η(8z)^(-1) η(10z)^8 η(15z) η(20z)^(-4) η(24z) η(30z)^(-3) η(40z) η(60z)^3 η(120z)^(-1)` at level 120. -/
abbrev cuspForm_120_eta_1m3_2p7_3p1_4m1_5m3_6m2_8m1_10p8_15p1_20m4_24p1_30m3_40p1_60p3_120m1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -3, 1 => 7, 2 => 1, 3 => -1, 4 => -3, 5 => -2, 7 => -1, 9 => 8, 14 => 1, 19 => -4, 23 => 1, 29 => -3, 39 => 1, 59 => 3, 119 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m3_2p7_3p1_4m1_5m3_6m2_8m1_10p8_15p1_20m4_24p1_30m3_40p1_60p3_120m1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m3_2p7_3p1_4m1_5m3_6m2_8m1_10p8_15p1_20m4_24p1_30m3_40p1_60p3_120m1 =
    [0, 1, 3, 2, 0, 0, 0, 8, 9, -1, 0, -10, -3, 12, -6, 1, -12, -20, 3, -12,
     3, 4, -6, 2, -6, 1, 0, 8, 6, 8, -3, -12, -3, -6, 12, 0, 0, -8, 0, 10,
     6, 6, -6, 18, -6, 10, 0, 2, 9, -27, 3, -18, -6, 0, 0, -10, -6, -8, -12, 34,
     0, 30, 12, -20, 24, 10, 6, 2, -6, 6, 6, 0, 9, -2, -12, 2, 12, 16, 6, -8,
     -9, -7, 6, -2, 6, -2, 0, 6, -30, 6, 0, 0, 0, -20, 12, -8, 6, 18, 3, 6] := by
  eta_coeff

end WeightTwoCusps
