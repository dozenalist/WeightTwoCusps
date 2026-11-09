module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«240».New.«240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(2z)^(-7) η(4z)^14 η(6z)^7 η(8z)^(-5) η(10z) η(12z)^(-7) η(20z)^(-2) η(24z)^2 η(30z)^(-1) η(40z) η(60z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-7) η(4z)^14 η(6z)^7 η(8z)^(-5) η(10z) η(12z)^(-7) η(20z)^(-2) η(24z)^2 η(30z)^(-1) η(40z) η(60z)` at level 480. -/
abbrev cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1_old_480_2 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1_old_480_2_eq_eta :
    cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1_old_480_2 =
      etaQuotientCuspForm 480 sparse![480; 1 => -7, 3 => 14, 5 => 7, 7 => -5, 9 => 1, 11 => -7, 19 => -2, 23 => 2, 29 => -1, 39 => 1, 59 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1_old_480_2_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1_old_480_2 =
    [0, 0, 1, 0, 7, 0, 21, 0, 35, 0, 33, 0, 13, 0, 0, 0, 15, 0, 41, 0,
     51, 0, 36, 0, 5, 0, -22, 0, -20, 0, 33, 0, 75, 0, 42, 0, -13, 0, -36, 0,
     -5, 0, 20, 0, 28, 0, 48, 0, -15, 0, -51, 0, -14, 0, 21, 0, 40, 0, -34, 0,
     -31, 0, -48, 0, -105, 0, -4, 0, 14, 0, -20, 0, -85, 0, -94, 0, 12, 0, -22, 0,
     15, 0, 54, 0, -60, 0, -104, 0, -60, 0, 13, 0, 4, 0, -80, 0, -75, 0, -67, 0] := by
  eta_coeff

end WeightTwoCusps
