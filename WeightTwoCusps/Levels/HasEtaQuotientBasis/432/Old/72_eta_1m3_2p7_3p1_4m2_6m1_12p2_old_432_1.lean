module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».New.«72_eta_1m3_2p7_3p1_4m2_6m1_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-1) η(12z)^2`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-1) η(12z)^2` at level 432. -/
abbrev cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_1 : gamma0CuspForms 432 :=
  gamma0RescaleToLevel cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_1_eq_eta :
    cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_1 =
      etaQuotientCuspForm 432 sparse![432; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 11 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_1_first_coeffs :
    first_coeffs 100 cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_432_1 =
    [0, 1, 3, 2, 0, 1, 0, 0, 0, -2, 0, -2, 0, -2, -12, -4, 0, -1, 0, -4,
     0, 0, 0, 4, 0, -1, 6, 2, 0, -3, 0, 8, 0, 8, 0, 0, 0, 6, 24, -4,
     0, 3, 0, 4, 0, 4, 0, 0, 0, -7, -15, 4, 0, 1, 0, -8, 0, -8, 0, -2,
     0, -2, -12, 0, 0, -2, 0, -4, 0, -16, 0, -4, 0, 10, -30, -2, 0, 0, 0, -8,
     0, -2, 0, 2, 0, -4, 24, 12, 0, 3, 0, 0, 0, 16, 0, -4, 0, 2, 27, -8] := by
  eta_coeff

end WeightTwoCusps
