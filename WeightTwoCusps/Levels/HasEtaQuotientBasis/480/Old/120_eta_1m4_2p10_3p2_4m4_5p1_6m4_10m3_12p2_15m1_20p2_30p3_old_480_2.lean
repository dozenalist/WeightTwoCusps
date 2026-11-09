module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«120».New.«120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(2z)^(-4) η(4z)^10 η(6z)^2 η(8z)^(-4) η(10z) η(12z)^(-4) η(20z)^(-3) η(24z)^2 η(30z)^(-1) η(40z)^2 η(60z)^3`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-4) η(4z)^10 η(6z)^2 η(8z)^(-4) η(10z) η(12z)^(-4) η(20z)^(-3) η(24z)^2 η(30z)^(-1) η(40z)^2 η(60z)^3` at level 480. -/
abbrev cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_480_2 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_480_2_eq_eta :
    cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_480_2 =
      etaQuotientCuspForm 480 sparse![480; 1 => -4, 3 => 10, 5 => 2, 7 => -4, 9 => 1, 11 => -4, 19 => -3, 23 => 2, 29 => -1, 39 => 2, 59 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_480_2_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_480_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 4, 0, -2, 0, -4, 0, -1, 0,
     -1, 0, 0, 0, 2, 0, 2, 0, -2, 0, -3, 0, 5, 0, 0, 0, -6, 0, 0, 0,
     -2, 0, -1, 0, 2, 0, 4, 0, 1, 0, -6, 0, 2, 0, 0, 0, -6, 0, 0, 0,
     -3, 0, -4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 0, -4, 0, 2, 0,
     -1, 0, -4, 0, 4, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, -2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
