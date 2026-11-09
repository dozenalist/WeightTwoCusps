module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(9z)^(-2) η(15z) η(18z) η(30z)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(9z)^(-2) η(15z) η(18z) η(30z)` at level 360. -/
abbrev cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_360_1 : gamma0CuspForms 360 :=
  gamma0RescaleToLevel cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_360_1_eq_eta :
    cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_360_1 =
      etaQuotientCuspForm 360 sparse![360; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 14 => 1, 17 => 1, 29 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_360_1_first_coeffs :
    first_coeffs 100 cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_360_1 =
    [0, 0, 1, 2, 4, 1, 0, -4, 1, 0, 0, -2, -2, 4, -2, 0, -4, -2, -2, -8,
     -1, -4, 4, 0, 0, 0, 0, 2, -4, 2, 2, 8, -3, -4, -8, -2, 4, 12, 0, 0,
     0, 8, 4, -8, 6, -2, 0, 4, 6, 16, 1, 8, -4, -2, 0, 4, -2, 0, 8, -2,
     -4, -8, 4, -4, 4, 0, -4, -16, -6, 0, -4, -4, -2, -8, -4, 2, 8, 0, -4, 8,
     3, 0, -4, 0, -4, -8, 0, -8, 4, -12, 0, -8, 0, 8, -8, 0, -8, 0, 1, 4] := by
  eta_coeff

end WeightTwoCusps
