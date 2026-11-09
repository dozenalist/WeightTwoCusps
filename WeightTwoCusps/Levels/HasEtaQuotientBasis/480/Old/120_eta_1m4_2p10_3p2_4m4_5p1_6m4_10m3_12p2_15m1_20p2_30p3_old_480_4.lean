module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«120».New.«120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(4z)^(-4) η(8z)^10 η(12z)^2 η(16z)^(-4) η(20z) η(24z)^(-4) η(40z)^(-3) η(48z)^2 η(60z)^(-1) η(80z)^2 η(120z)^3`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-4) η(8z)^10 η(12z)^2 η(16z)^(-4) η(20z) η(24z)^(-4) η(40z)^(-3) η(48z)^2 η(60z)^(-1) η(80z)^2 η(120z)^3` at level 480. -/
abbrev cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_480_4 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_480_4_eq_eta :
    cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_480_4 =
      etaQuotientCuspForm 480 sparse![480; 3 => -4, 7 => 10, 11 => 2, 15 => -4, 19 => 1, 23 => -4, 39 => -3, 47 => 2, 59 => -1, 79 => 2, 119 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_480_4_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_480_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     4, 0, 0, 0, 4, 0, 0, 0, -2, 0, 0, 0, -4, 0, 0, 0, -1, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0,
     -3, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
