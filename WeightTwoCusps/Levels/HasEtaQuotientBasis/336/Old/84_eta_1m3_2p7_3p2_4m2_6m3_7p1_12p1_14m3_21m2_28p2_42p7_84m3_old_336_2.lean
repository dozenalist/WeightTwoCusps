module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».New.«84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(2z)^(-3) η(4z)^7 η(6z)^2 η(8z)^(-2) η(12z)^(-3) η(14z) η(24z) η(28z)^(-3) η(42z)^(-2) η(56z)^2 η(84z)^7 η(168z)^(-3)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^7 η(6z)^2 η(8z)^(-2) η(12z)^(-3) η(14z) η(24z) η(28z)^(-3) η(42z)^(-2) η(56z)^2 η(84z)^7 η(168z)^(-3)` at level 336. -/
abbrev cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_336_2 : gamma0CuspForms 336 :=
  gamma0RescaleToLevel cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_336_2_eq_eta :
    cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_336_2 =
      etaQuotientCuspForm 336 sparse![336; 1 => -3, 3 => 7, 5 => 2, 7 => -2, 11 => -3, 13 => 1, 23 => 1, 27 => -3, 41 => -2, 55 => 2, 83 => 7, 167 => -3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_336_2_first_coeffs :
    first_coeffs 100 cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_336_2 =
    [0, 0, 1, 0, 3, 0, 2, 0, -1, 0, -2, 0, -2, 0, 1, 0, 1, 0, -3, 0,
     -4, 0, -6, 0, 0, 0, 4, 0, -1, 0, 2, 0, 3, 0, 4, 0, 3, 0, -2, 0,
     0, 0, 2, 0, 0, 0, -2, 0, -4, 0, -9, 0, 0, 0, 4, 0, -1, 0, 2, 0,
     0, 0, 4, 0, 1, 0, -2, 0, 2, 0, 2, 0, -1, 0, -2, 0, 2, 0, -8, 0,
     0, 0, 8, 0, -2, 0, 0, 0, -8, 0, -2, 0, 8, 0, 0, 0, 4, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
