module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«240».New.«240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(2z)^(-5) η(4z)^13 η(6z) η(8z)^(-5) η(10z)^(-1) η(12z)^(-4) η(20z)^(-1) η(24z)^2 η(30z)^5 η(40z) η(60z)^(-2)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-5) η(4z)^13 η(6z) η(8z)^(-5) η(10z)^(-1) η(12z)^(-4) η(20z)^(-1) η(24z)^2 η(30z)^5 η(40z) η(60z)^(-2)` at level 480. -/
abbrev cuspForm_240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2_old_480_2 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2_old_480_2_eq_eta :
    cuspForm_240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2_old_480_2 =
      etaQuotientCuspForm 480 sparse![480; 1 => -5, 3 => 13, 5 => 1, 7 => -5, 9 => -1, 11 => -4, 19 => -1, 23 => 2, 29 => 5, 39 => 1, 59 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2_old_480_2_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m5_2p13_3p1_4m5_5m1_6m4_10m1_12p2_15p5_20p1_30m2_old_480_2 =
    [0, 0, 1, 0, 5, 0, 7, 0, -1, 0, -5, 0, 5, 0, 8, 0, 9, 0, 9, 0,
     -9, 0, 0, 0, 23, 0, 14, 0, 8, 0, -7, 0, -9, 0, 6, 0, 1, 0, 20, 0,
     1, 0, -16, 0, 8, 0, -12, 0, 9, 0, 5, 0, -22, 0, -5, 0, -20, 0, 10, 0,
     7, 0, -16, 0, 9, 0, -8, 0, -2, 0, -12, 0, -25, 0, 14, 0, 12, 0, -6, 0,
     -9, 0, -18, 0, 0, 0, 4, 0, 0, 0, -9, 0, -28, 0, 20, 0, -9, 0, -11, 0] := by
  eta_coeff

end WeightTwoCusps
