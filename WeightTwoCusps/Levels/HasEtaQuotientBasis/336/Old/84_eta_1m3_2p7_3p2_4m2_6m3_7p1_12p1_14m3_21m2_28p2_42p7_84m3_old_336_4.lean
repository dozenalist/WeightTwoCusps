module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».New.«84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(4z)^(-3) η(8z)^7 η(12z)^2 η(16z)^(-2) η(24z)^(-3) η(28z) η(48z) η(56z)^(-3) η(84z)^(-2) η(112z)^2 η(168z)^7 η(336z)^(-3)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-3) η(8z)^7 η(12z)^2 η(16z)^(-2) η(24z)^(-3) η(28z) η(48z) η(56z)^(-3) η(84z)^(-2) η(112z)^2 η(168z)^7 η(336z)^(-3)` at level 336. -/
abbrev cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_336_4 : gamma0CuspForms 336 :=
  gamma0Rescale cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_336_4_eq_eta :
    cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_336_4 =
      etaQuotientCuspForm 336 sparse![336; 3 => -3, 7 => 7, 11 => 2, 15 => -2, 23 => -3, 27 => 1, 47 => 1, 55 => -3, 83 => -2, 111 => 2, 167 => 7, 335 => -3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_336_4_first_coeffs :
    first_coeffs 100 cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_336_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0,
     -2, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -3, 0, 0, 0,
     -4, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -1, 0, 0, 0,
     2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -4, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
