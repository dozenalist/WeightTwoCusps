module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m2_2p4_3p2_4m1_5p2_6m2_10m2_12p1_15m2_20p1_30p4_60m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(5z)^2 η(6z)^(-2) η(10z)^(-2) η(12z) η(15z)^(-2) η(20z) η(30z)^4 η(60z)^(-1)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_60_eta_1m2_2p4_3p2_4m1_5p2_6m2_10m2_12p1_15m2_20p1_30p4_60m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(5z)^2 η(6z)^(-2) η(10z)^(-2) η(12z) η(15z)^(-2) η(20z) η(30z)^4 η(60z)^(-1)` at level 300. -/
abbrev cuspForm_60_eta_1m2_2p4_3p2_4m1_5p2_6m2_10m2_12p1_15m2_20p1_30p4_60m1_old_300_1 : gamma0CuspForms 300 :=
  gamma0RescaleToLevel cuspForm_60_eta_1m2_2p4_3p2_4m1_5p2_6m2_10m2_12p1_15m2_20p1_30p4_60m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_60_eta_1m2_2p4_3p2_4m1_5p2_6m2_10m2_12p1_15m2_20p1_30p4_60m1_old_300_1_eq_eta :
    cuspForm_60_eta_1m2_2p4_3p2_4m1_5p2_6m2_10m2_12p1_15m2_20p1_30p4_60m1_old_300_1 =
      etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 4 => 2, 5 => -2, 9 => -2, 11 => 1, 14 => -2, 19 => 1, 29 => 4, 59 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_60_eta_1m2_2p4_3p2_4m1_5p2_6m2_10m2_12p1_15m2_20p1_30p4_60m1_old_300_1_first_coeffs :
    first_coeffs 100 cuspForm_60_eta_1m2_2p4_3p2_4m1_5p2_6m2_10m2_12p1_15m2_20p1_30p4_60m1_old_300_1 =
    [0, 0, 1, 2, 1, 0, -1, -2, -3, -2, 1, 0, -1, 0, 0, -2, 1, 4, 1, 0,
     1, 2, -4, -2, 3, 0, -2, 0, 0, -4, -1, 4, 5, 0, 2, 2, 1, 0, 4, 4,
     -3, -4, 0, 2, -4, 2, 0, 2, -1, 4, 1, -8, -2, 0, -1, 0, 0, -8, -2, -4,
     -1, -4, 0, -6, -7, 0, 4, -2, 2, 10, 0, 4, -3, 0, -10, 2, 4, 0, 2, 0,
     1, 8, 10, 2, 0, -4, 4, 8, 12, 8, 1, -4, 0, -4, 8, 0, -5, 0, -7, 0] := by
  eta_coeff

end WeightTwoCusps
