module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».New.«84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(5z)^(-3) η(10z)^7 η(15z)^2 η(20z)^(-2) η(30z)^(-3) η(35z) η(60z) η(70z)^(-3) η(105z)^(-2) η(140z)^2 η(210z)^7 η(420z)^(-3)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-3) η(10z)^7 η(15z)^2 η(20z)^(-2) η(30z)^(-3) η(35z) η(60z) η(70z)^(-3) η(105z)^(-2) η(140z)^2 η(210z)^7 η(420z)^(-3)` at level 420. -/
abbrev cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_420_5 : gamma0CuspForms 420 :=
  gamma0Rescale cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_420_5_eq_eta :
    cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_420_5 =
      etaQuotientCuspForm 420 sparse![420; 4 => -3, 9 => 7, 14 => 2, 19 => -2, 29 => -3, 34 => 1, 59 => 1, 69 => -3, 104 => -2, 139 => 2, 209 => 7, 419 => -3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_420_5_first_coeffs :
    first_coeffs 100 cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_old_420_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     1, 0, 0, 0, 0, -3, 0, 0, 0, 0, -4, 0, 0, 0, 0, -6, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 4, 0, 0, 0, 0, -1, 0, 0, 0, 0, 2, 0, 0, 0, 0,
     3, 0, 0, 0, 0, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, -2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
