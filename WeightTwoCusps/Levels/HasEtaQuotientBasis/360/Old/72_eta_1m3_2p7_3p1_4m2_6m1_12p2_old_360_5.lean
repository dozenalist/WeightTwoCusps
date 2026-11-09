module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».New.«72_eta_1m3_2p7_3p1_4m2_6m1_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(5z)^(-3) η(10z)^7 η(15z) η(20z)^(-2) η(30z)^(-1) η(60z)^2`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-3) η(10z)^7 η(15z) η(20z)^(-2) η(30z)^(-1) η(60z)^2` at level 360. -/
abbrev cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_360_5 : gamma0CuspForms 360 :=
  gamma0Rescale cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_360_5_eq_eta :
    cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_360_5 =
      etaQuotientCuspForm 360 sparse![360; 4 => -3, 9 => 7, 14 => 1, 19 => -2, 29 => -1, 59 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_360_5_first_coeffs :
    first_coeffs 100 cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_360_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -12, 0, 0, 0, 0, -4, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
