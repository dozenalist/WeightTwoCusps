module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«120».New.«120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(5z) η(6z)^(-4) η(10z)^(-3) η(12z)^2 η(15z)^(-1) η(20z)^2 η(30z)^3`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(5z) η(6z)^(-4) η(10z)^(-3) η(12z)^2 η(15z)^(-1) η(20z)^2 η(30z)^3` at level 240. -/
abbrev cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_240_1 : gamma0CuspForms 240 :=
  gamma0RescaleToLevel cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_240_1_eq_eta :
    cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_240_1 =
      etaQuotientCuspForm 240 sparse![240; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 4 => 1, 5 => -4, 9 => -3, 11 => 2, 14 => -1, 19 => 2, 29 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_240_1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_240_1 =
    [0, 0, 0, 0, 1, 4, 4, -2, -4, -1, -1, 0, 2, 2, -2, -3, 5, 0, -6, 0,
     -2, -1, 2, 4, 1, -6, 2, 0, -6, 0, -3, -4, 0, 0, 2, 0, 1, 2, -4, 2,
     -1, -4, 4, 0, 2, 3, 0, 0, -2, 0, 0, 0, 4, 0, 4, 14, 6, -2, -2, 0,
     -1, 0, 4, 2, -7, -8, -2, 4, 8, 1, 2, 0, -4, 0, 6, 6, -8, -4, 6, -4,
     2, 2, -8, -8, -6, 6, -4, 2, 10, 0, 5, 8, 0, 0, -4, -12, -3, -4, 8, -4] := by
  eta_coeff

end WeightTwoCusps
