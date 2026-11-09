module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«120».New.«120_eta_1m3_2p5_3p1_4p2_5p3_6m2_8m2_10m2_12p1_15m1_20m1_30p1_40p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-3) η(2z)^5 η(3z) η(4z)^2 η(5z)^3 η(6z)^(-2) η(8z)^(-2) η(10z)^(-2) η(12z) η(15z)^(-1) η(20z)^(-1) η(30z) η(40z)^2`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_120_eta_1m3_2p5_3p1_4p2_5p3_6m2_8m2_10m2_12p1_15m1_20m1_30p1_40p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z) η(4z)^2 η(5z)^3 η(6z)^(-2) η(8z)^(-2) η(10z)^(-2) η(12z) η(15z)^(-1) η(20z)^(-1) η(30z) η(40z)^2` at level 240. -/
abbrev cuspForm_120_eta_1m3_2p5_3p1_4p2_5p3_6m2_8m2_10m2_12p1_15m1_20m1_30p1_40p2_old_240_1 : gamma0CuspForms 240 :=
  gamma0RescaleToLevel cuspForm_120_eta_1m3_2p5_3p1_4p2_5p3_6m2_8m2_10m2_12p1_15m1_20m1_30p1_40p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_120_eta_1m3_2p5_3p1_4p2_5p3_6m2_8m2_10m2_12p1_15m1_20m1_30p1_40p2_old_240_1_eq_eta :
    cuspForm_120_eta_1m3_2p5_3p1_4p2_5p3_6m2_8m2_10m2_12p1_15m1_20m1_30p1_40p2_old_240_1 =
      etaQuotientCuspForm 240 sparse![240; 0 => -3, 1 => 5, 2 => 1, 3 => 2, 4 => 3, 5 => -2, 7 => -2, 9 => -2, 11 => 1, 14 => -1, 19 => -1, 29 => 1, 39 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m3_2p5_3p1_4p2_5p3_6m2_8m2_10m2_12p1_15m1_20m1_30p1_40p2_old_240_1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m3_2p5_3p1_4p2_5p3_6m2_8m2_10m2_12p1_15m1_20m1_30p1_40p2_old_240_1 =
    [0, 0, 0, 1, 3, 4, 6, 6, 0, -2, -3, -7, 0, 7, 0, -1, -3, -17, -12, -2,
     0, 5, 6, 5, -3, -3, 6, 4, -6, 5, -3, -20, 0, -3, -6, -4, 3, -7, -12, 5,
     3, 6, 6, 13, -6, 8, 6, 5, 6, -18, 0, -15, 0, 9, 12, 5, 6, -4, 6, 19,
     -3, 28, 0, -4, 9, 3, -6, 9, 12, 0, 0, 0, 0, -10, 18, 4, 0, 4, 6, -10,
     -6, -2, -12, -17, -6, 7, -18, 9, -6, -6, 9, 8, 0, -16, -18, -18, -3, 4, 12, -3] := by
  eta_coeff

end WeightTwoCusps
