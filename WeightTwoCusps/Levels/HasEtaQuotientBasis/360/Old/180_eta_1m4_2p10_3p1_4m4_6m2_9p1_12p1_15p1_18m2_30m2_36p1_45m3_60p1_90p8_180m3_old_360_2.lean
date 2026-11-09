module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«180».New.«180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(2z)^(-4) η(4z)^10 η(6z) η(8z)^(-4) η(12z)^(-2) η(18z) η(24z) η(30z) η(36z)^(-2) η(60z)^(-2) η(72z) η(90z)^(-3) η(120z) η(180z)^8 η(360z)^(-3)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-4) η(4z)^10 η(6z) η(8z)^(-4) η(12z)^(-2) η(18z) η(24z) η(30z) η(36z)^(-2) η(60z)^(-2) η(72z) η(90z)^(-3) η(120z) η(180z)^8 η(360z)^(-3)` at level 360. -/
abbrev cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3_old_360_2 : gamma0CuspForms 360 :=
  gamma0Rescale cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3_old_360_2_eq_eta :
    cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3_old_360_2 =
      etaQuotientCuspForm 360 sparse![360; 1 => -4, 3 => 10, 5 => 1, 7 => -4, 11 => -2, 17 => 1, 23 => 1, 29 => 1, 35 => -2, 59 => -2, 71 => 1, 89 => -3, 119 => 1, 179 => 8, 359 => -3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3_old_360_2_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3_old_360_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 4, 0, -1, 0, 0, 0, 4, 0, 1, 0,
     0, 0, 0, 0, 1, 0, 0, 0, -8, 0, -1, 0, 0, 0, -8, 0, -1, 0, -4, 0,
     0, 0, 0, 0, -8, 0, 4, 0, -1, 0, 0, 0, 8, 0, -3, 0, 0, 0, 4, 0,
     1, 0, 0, 0, -8, 0, 0, 0, 4, 0, -16, 0, 1, 0, 8, 0, -4, 0, 2, 0,
     -4, 0, 12, 0, 4, 0, 0, 0, 16, 0, -1, 0, 0, 0, 0, 0, 1, 0, 4, 0] := by
  eta_coeff

end WeightTwoCusps
