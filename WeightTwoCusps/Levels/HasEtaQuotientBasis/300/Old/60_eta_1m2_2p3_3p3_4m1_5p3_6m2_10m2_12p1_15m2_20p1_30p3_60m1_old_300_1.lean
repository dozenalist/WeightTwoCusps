module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m2_2p3_3p3_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(5z)^3 η(6z)^(-2) η(10z)^(-2) η(12z) η(15z)^(-2) η(20z) η(30z)^3 η(60z)^(-1)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_60_eta_1m2_2p3_3p3_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(4z)^(-1) η(5z)^3 η(6z)^(-2) η(10z)^(-2) η(12z) η(15z)^(-2) η(20z) η(30z)^3 η(60z)^(-1)` at level 300. -/
abbrev cuspForm_60_eta_1m2_2p3_3p3_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1_old_300_1 : gamma0CuspForms 300 :=
  gamma0RescaleToLevel cuspForm_60_eta_1m2_2p3_3p3_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_60_eta_1m2_2p3_3p3_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1_old_300_1_eq_eta :
    cuspForm_60_eta_1m2_2p3_3p3_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1_old_300_1 =
      etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 4 => 3, 5 => -2, 9 => -2, 11 => 1, 14 => -2, 19 => 1, 29 => 3, 59 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_60_eta_1m2_2p3_3p3_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1_old_300_1_first_coeffs :
    first_coeffs 100 cuspForm_60_eta_1m2_2p3_3p3_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1_old_300_1 =
    [0, 1, 2, 2, 1, 0, -1, -4, -4, -1, 1, -2, -2, 0, -2, -3, 1, 8, 2, 0,
     2, 0, -6, -2, 5, 1, -2, 0, 2, -8, -2, 8, 8, 2, 6, 4, 1, -4, 4, 6,
     -5, -2, -2, 2, -6, 2, 0, 6, -2, 5, 2, -6, -4, -8, -1, -2, -2, -12, -6, -6,
     -1, -10, 4, -8, -11, -2, 6, 2, 0, 10, 2, 0, -4, 6, -14, 2, 8, 0, 4, 4,
     2, 9, 12, 14, 2, -6, 4, 6, 18, 14, 1, -8, 0, 0, 12, 4, -7, 2, -6, -2] := by
  eta_coeff

end WeightTwoCusps
