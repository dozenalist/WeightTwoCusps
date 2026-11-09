module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».New.«72_eta_1m3_2p7_3p1_4m2_6m1_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(6z)^(-3) η(12z)^7 η(18z) η(24z)^(-2) η(36z)^(-1) η(72z)^2`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-3) η(12z)^7 η(18z) η(24z)^(-2) η(36z)^(-1) η(72z)^2` at level 432. -/
abbrev cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_6 : gamma0CuspForms 432 :=
  gamma0Rescale cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_6_eq_eta :
    cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_6 =
      etaQuotientCuspForm 432 sparse![432; 5 => -3, 11 => 7, 17 => 1, 23 => -2, 35 => -1, 71 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_6_first_coeffs :
    first_coeffs 100 cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_6 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0,
     0, 0, 0, 0, -12, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
