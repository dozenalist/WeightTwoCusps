module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«120».New.«120_eta_1m1_2m2_3p2_4p6_5p2_6p1_8m2_10p1_12m3_15m1_20m3_24p1_30m2_40p1_60p6_120m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-1) η(2z)^(-2) η(3z)^2 η(4z)^6 η(5z)^2 η(6z) η(8z)^(-2) η(10z) η(12z)^(-3) η(15z)^(-1) η(20z)^(-3) η(24z) η(30z)^(-2) η(40z) η(60z)^6 η(120z)^(-2)`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_120_eta_1m1_2m2_3p2_4p6_5p2_6p1_8m2_10p1_12m3_15m1_20m3_24p1_30m2_40p1_60p6_120m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-2) η(3z)^2 η(4z)^6 η(5z)^2 η(6z) η(8z)^(-2) η(10z) η(12z)^(-3) η(15z)^(-1) η(20z)^(-3) η(24z) η(30z)^(-2) η(40z) η(60z)^6 η(120z)^(-2)` at level 240. -/
abbrev cuspForm_120_eta_1m1_2m2_3p2_4p6_5p2_6p1_8m2_10p1_12m3_15m1_20m3_24p1_30m2_40p1_60p6_120m2_old_240_1 : gamma0CuspForms 240 :=
  gamma0RescaleToLevel cuspForm_120_eta_1m1_2m2_3p2_4p6_5p2_6p1_8m2_10p1_12m3_15m1_20m3_24p1_30m2_40p1_60p6_120m2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_120_eta_1m1_2m2_3p2_4p6_5p2_6p1_8m2_10p1_12m3_15m1_20m3_24p1_30m2_40p1_60p6_120m2_old_240_1_eq_eta :
    cuspForm_120_eta_1m1_2m2_3p2_4p6_5p2_6p1_8m2_10p1_12m3_15m1_20m3_24p1_30m2_40p1_60p6_120m2_old_240_1 =
      etaQuotientCuspForm 240 sparse![240; 0 => -1, 1 => -2, 2 => 2, 3 => 6, 4 => 2, 5 => 1, 7 => -2, 9 => 1, 11 => -3, 14 => -1, 19 => -3, 23 => 1, 29 => -2, 39 => 1, 59 => 6, 119 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m1_2m2_3p2_4p6_5p2_6p1_8m2_10p1_12m3_15m1_20m3_24p1_30m2_40p1_60p6_120m2_old_240_1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m1_2m2_3p2_4p6_5p2_6p1_8m2_10p1_12m3_15m1_20m3_24p1_30m2_40p1_60p6_120m2_old_240_1 =
    [0, 0, 1, 1, 4, 3, 6, 2, 3, -2, -2, -4, -5, -4, -10, -4, -12, 0, -3, 8,
     5, 6, 2, -2, -2, -2, 4, -1, 2, -4, -5, -4, 7, 4, 16, -2, 4, -12, -8, 2,
     2, 12, -2, 6, -18, 5, -4, 10, 11, -4, 1, -14, -10, 0, 2, 4, -2, -8, -16, -8,
     -4, 4, 20, -2, 16, -2, -2, 10, 6, 6, 10, -4, 3, 0, 8, 3, 20, 0, 10, 0,
     -11, 8, -22, 6, 2, 6, -4, 14, -10, -8, 2, -4, 0, -8, 0, -8, -6, 0, 25, -4] := by
  eta_coeff

end WeightTwoCusps
