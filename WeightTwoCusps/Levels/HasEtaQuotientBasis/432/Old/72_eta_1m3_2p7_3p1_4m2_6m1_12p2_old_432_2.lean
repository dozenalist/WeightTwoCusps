module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».New.«72_eta_1m3_2p7_3p1_4m2_6m1_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(2z)^(-3) η(4z)^7 η(6z) η(8z)^(-2) η(12z)^(-1) η(24z)^2`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^7 η(6z) η(8z)^(-2) η(12z)^(-1) η(24z)^2` at level 432. -/
abbrev cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_2 : gamma0CuspForms 432 :=
  gamma0RescaleToLevel cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_2_eq_eta :
    cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_2 =
      etaQuotientCuspForm 432 sparse![432; 1 => -3, 3 => 7, 5 => 1, 7 => -2, 11 => -1, 23 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_2_first_coeffs :
    first_coeffs 100 cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_2 =
    [0, 0, 1, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0,
     0, 0, -2, 0, 0, 0, -2, 0, -12, 0, -4, 0, 0, 0, -1, 0, 0, 0, -4, 0,
     0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -1, 0, 6, 0, 2, 0, 0, 0, -3, 0,
     0, 0, 8, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 6, 0, 24, 0, -4, 0,
     0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -7, 0] := by
  eta_coeff

end WeightTwoCusps
