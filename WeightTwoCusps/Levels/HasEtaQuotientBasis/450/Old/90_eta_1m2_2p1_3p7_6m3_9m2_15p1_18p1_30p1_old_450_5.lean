module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(5z)^(-2) η(10z) η(15z)^7 η(30z)^(-3) η(45z)^(-2) η(75z) η(90z) η(150z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-2) η(10z) η(15z)^7 η(30z)^(-3) η(45z)^(-2) η(75z) η(90z) η(150z)` at level 450. -/
abbrev cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_450_5 : gamma0CuspForms 450 :=
  gamma0Rescale cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_450_5_eq_eta :
    cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_450_5 =
      etaQuotientCuspForm 450 sparse![450; 4 => -2, 9 => 1, 14 => 7, 29 => -3, 44 => -2, 74 => 1, 89 => 1, 149 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_450_5_first_coeffs :
    first_coeffs 100 cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_old_450_5 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0,
     4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 4, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -4, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -8, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
