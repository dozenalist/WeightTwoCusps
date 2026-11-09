module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m2_2p3_3p2_5p1_6m1_15p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z) η(6z)^(-1) η(15z)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z) η(6z)^(-1) η(15z)` at level 360. -/
abbrev cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1_old_360_1 : gamma0CuspForms 360 :=
  gamma0RescaleToLevel cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1_old_360_1_eq_eta :
    cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1_old_360_1 =
      etaQuotientCuspForm 360 sparse![360; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 14 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1_old_360_1_first_coeffs :
    first_coeffs 100 cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1_old_360_1 =
    [0, 1, 2, 2, 2, 1, 1, 0, 0, 1, -1, -1, -2, -2, -3, -1, -1, -4, -4, -5,
     -1, -6, -2, 0, -3, 1, -1, 2, 0, 4, 4, 0, -2, -2, 1, -3, 5, 8, 2, 2,
     0, 7, 6, 4, 7, -2, 0, 2, 10, 2, 2, 10, -4, 2, 1, 5, -3, -4, 8, -1,
     -5, -2, 6, -6, 4, 1, -10, -6, -8, 0, -3, -2, 0, -8, -11, 2, -1, 0, -8, 0,
     5, 1, -4, -6, -6, -7, 2, -10, -6, -15, -1, -9, 0, 12, -5, -2, -7, 2, -2, 2] := by
  eta_coeff

end WeightTwoCusps
