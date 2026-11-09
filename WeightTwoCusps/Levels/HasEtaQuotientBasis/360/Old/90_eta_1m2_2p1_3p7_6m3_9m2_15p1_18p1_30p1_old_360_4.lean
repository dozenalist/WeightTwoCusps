module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(4z)^(-2) η(8z) η(12z)^7 η(24z)^(-3) η(36z)^(-2) η(60z) η(72z) η(120z)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z) η(12z)^7 η(24z)^(-3) η(36z)^(-2) η(60z) η(72z) η(120z)` at level 360. -/
abbrev cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_360_4 : gamma0CuspForms 360 :=
  gamma0Rescale cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_360_4_eq_eta :
    cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_360_4 =
      etaQuotientCuspForm 360 sparse![360; 3 => -2, 7 => 1, 11 => 7, 23 => -3, 35 => -2, 59 => 1, 71 => 1, 119 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_360_4_first_coeffs :
    first_coeffs 100 cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_360_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 4, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 0, -4, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, -8, 0, 0, 0,
     -1, 0, 0, 0, -4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
