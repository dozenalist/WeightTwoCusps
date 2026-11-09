module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«120».New.«120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(2z)^(-5) η(4z)^11 η(6z) η(8z)^(-4) η(10z)^5 η(12z)^(-2) η(20z)^(-4) η(24z) η(30z)^(-1) η(40z) η(60z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-5) η(4z)^11 η(6z) η(8z)^(-4) η(10z)^5 η(12z)^(-2) η(20z)^(-4) η(24z) η(30z)^(-1) η(40z) η(60z)` at level 480. -/
abbrev cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_480_2 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_480_2_eq_eta :
    cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_480_2 =
      etaQuotientCuspForm 480 sparse![480; 1 => -5, 3 => 11, 5 => 1, 7 => -4, 9 => 5, 11 => -2, 19 => -4, 23 => 1, 29 => -1, 39 => 1, 59 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_480_2_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_480_2 =
    [0, 0, 1, 0, 5, 0, 9, 0, 9, 0, 13, 0, 17, 0, 2, 0, -9, 0, 3, 0,
     -5, 0, -20, 0, 9, 0, 22, 0, -8, 0, -3, 0, 9, 0, -22, 0, -31, 0, -8, 0,
     -9, 0, -18, 0, 0, 0, 10, 0, -9, 0, -11, 0, 10, 0, -9, 0, -36, 0, -14, 0,
     -17, 0, -32, 0, -9, 0, 12, 0, 6, 0, 2, 0, 9, 0, -18, 0, -20, 0, 6, 0,
     9, 0, -6, 0, 16, 0, 34, 0, 0, 0, 15, 0, 12, 0, 22, 0, 9, 0, -15, 0] := by
  eta_coeff

end WeightTwoCusps
