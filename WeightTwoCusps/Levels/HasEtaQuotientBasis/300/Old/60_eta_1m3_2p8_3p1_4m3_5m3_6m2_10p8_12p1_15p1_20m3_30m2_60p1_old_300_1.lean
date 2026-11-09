module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(5z)^(-3) η(6z)^(-2) η(10z)^8 η(12z) η(15z) η(20z)^(-3) η(30z)^(-2) η(60z)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(5z)^(-3) η(6z)^(-2) η(10z)^8 η(12z) η(15z) η(20z)^(-3) η(30z)^(-2) η(60z)` at level 300. -/
abbrev cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1_old_300_1 : gamma0CuspForms 300 :=
  gamma0RescaleToLevel cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1_old_300_1_eq_eta :
    cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1_old_300_1 =
      etaQuotientCuspForm 300 sparse![300; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 4 => -3, 5 => -2, 9 => 8, 11 => 1, 14 => 1, 19 => -3, 29 => -2, 59 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1_old_300_1_first_coeffs :
    first_coeffs 100 cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1_old_300_1 =
    [0, 1, 3, 1, -3, -1, 3, 8, 3, -11, -3, 0, -3, 2, -12, -1, -3, -18, 3, -4,
     3, 8, 0, 12, 3, 1, 6, 13, 12, 18, -3, -16, 3, 0, 18, -8, -3, 2, -12, 2,
     -3, 18, -12, -16, 0, 11, 0, -12, -3, -15, 3, -18, -6, -6, 3, 0, -12, -4, -18, 24,
     3, 14, 24, -16, -3, -2, 0, 8, -18, 12, 12, -24, 3, 2, 6, 1, 12, 0, 6, 8,
     3, 1, -18, 0, 12, 18, -12, 18, 0, -30, -3, 16, 0, -16, 0, 4, 3, 2, 27, 0] := by
  eta_coeff

end WeightTwoCusps
