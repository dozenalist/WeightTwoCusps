module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«180».New.«180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(9z) η(12z) η(15z) η(18z)^(-2) η(30z)^(-2) η(36z) η(45z)^(-3) η(60z) η(90z)^8 η(180z)^(-3)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(9z) η(12z) η(15z) η(18z)^(-2) η(30z)^(-2) η(36z) η(45z)^(-3) η(60z) η(90z)^8 η(180z)^(-3)` at level 360. -/
abbrev cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3_old_360_1 : gamma0CuspForms 360 :=
  gamma0RescaleToLevel cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3_old_360_1_eq_eta :
    cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3_old_360_1 =
      etaQuotientCuspForm 360 sparse![360; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 8 => 1, 11 => 1, 14 => 1, 17 => -2, 29 => -2, 35 => 1, 44 => -3, 59 => 1, 89 => 8, 179 => -3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3_old_360_1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_15p1_18m2_30m2_36p1_45m3_60p1_90p8_180m3_old_360_1 =
    [0, 0, 0, 1, 4, 4, -1, 0, 4, 1, 0, 0, 1, 0, -8, -1, 0, -8, -1, -4,
     0, 0, -8, 4, -1, 0, 8, -3, 0, 4, 1, 0, -8, 0, 4, -16, 1, 8, -4, 2,
     -4, 12, 4, 0, 16, -1, 0, 0, 1, 4, 0, -2, -8, -8, -1, 4, -8, -4, 8, 8,
     -1, 0, 16, 0, -4, 4, 0, -8, -20, 4, -4, -16, -1, -8, 0, 1, 4, 4, -2, 0,
     4, 5, 8, 8, -4, -4, -16, 2, 8, -12, 1, -4, 0, 0, 4, 28, -1, 0, 20, 0] := by
  eta_coeff

end WeightTwoCusps
