module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m3_2p7_3p2_4m2_5p2_6m3_10m3_12p1_15m3_20p1_30p7_60m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-2) η(5z)^2 η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-3) η(20z) η(30z)^7 η(60z)^(-2)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_60_eta_1m3_2p7_3p2_4m2_5p2_6m3_10m3_12p1_15m3_20p1_30p7_60m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-2) η(5z)^2 η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-3) η(20z) η(30z)^7 η(60z)^(-2)` at level 300. -/
abbrev cuspForm_60_eta_1m3_2p7_3p2_4m2_5p2_6m3_10m3_12p1_15m3_20p1_30p7_60m2_old_300_1 : gamma0CuspForms 300 :=
  gamma0RescaleToLevel cuspForm_60_eta_1m3_2p7_3p2_4m2_5p2_6m3_10m3_12p1_15m3_20p1_30p7_60m2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_60_eta_1m3_2p7_3p2_4m2_5p2_6m3_10m3_12p1_15m3_20p1_30p7_60m2_old_300_1_eq_eta :
    cuspForm_60_eta_1m3_2p7_3p2_4m2_5p2_6m3_10m3_12p1_15m3_20p1_30p7_60m2_old_300_1 =
      etaQuotientCuspForm 300 sparse![300; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 4 => 2, 5 => -3, 9 => -3, 11 => 1, 14 => -3, 19 => 1, 29 => 7, 59 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_60_eta_1m3_2p7_3p2_4m2_5p2_6m3_10m3_12p1_15m3_20p1_30p7_60m2_old_300_1_first_coeffs :
    first_coeffs 100 cuspForm_60_eta_1m3_2p7_3p2_4m2_5p2_6m3_10m3_12p1_15m3_20p1_30p7_60m2_old_300_1 =
    [0, 0, 1, 3, 2, -1, -2, -4, -5, -2, 2, 2, -1, 2, 2, -2, 2, 6, 1, -4,
     1, 0, -6, -2, 4, 0, -4, 1, -2, -6, -1, 8, 7, -2, 0, 4, 2, 6, 8, 4,
     -4, -12, 2, -2, -6, 1, 0, -2, -1, 12, 1, -4, -2, 2, -2, 2, 2, -8, 0, -2,
     -2, -8, -4, -8, -10, 0, 6, -10, 6, 10, -2, 8, -5, -4, -16, 3, 4, 0, 2, 4,
     1, 8, 18, 2, -2, -8, 8, 4, 18, 20, 2, -8, 0, 0, 12, 0, -8, 0, -15, 2] := by
  eta_coeff

end WeightTwoCusps
