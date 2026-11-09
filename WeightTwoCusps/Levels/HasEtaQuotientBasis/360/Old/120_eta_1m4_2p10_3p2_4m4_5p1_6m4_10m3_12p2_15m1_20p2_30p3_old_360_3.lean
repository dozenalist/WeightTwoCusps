module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«120».New.«120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(3z)^(-4) η(6z)^10 η(9z)^2 η(12z)^(-4) η(15z) η(18z)^(-4) η(30z)^(-3) η(36z)^2 η(45z)^(-1) η(60z)^2 η(90z)^3`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-4) η(6z)^10 η(9z)^2 η(12z)^(-4) η(15z) η(18z)^(-4) η(30z)^(-3) η(36z)^2 η(45z)^(-1) η(60z)^2 η(90z)^3` at level 360. -/
abbrev cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_360_3 : gamma0CuspForms 360 :=
  gamma0Rescale cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_360_3_eq_eta :
    cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_360_3 =
      etaQuotientCuspForm 360 sparse![360; 2 => -4, 5 => 10, 8 => 2, 11 => -4, 14 => 1, 17 => -4, 29 => -3, 35 => 2, 44 => -1, 59 => 2, 89 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_360_3_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_old_360_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 4, 0,
     0, -2, 0, 0, -4, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0, 2,
     0, 0, -2, 0, 0, -3, 0, 0, 5, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0,
     -2, 0, 0, -1, 0, 0, 2, 0, 0, 4, 0, 0, 1, 0, 0, -6, 0, 0, 2, 0,
     0, 0, 0, 0, -6, 0, 0, 0, 0, 0, -3, 0, 0, -4, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
