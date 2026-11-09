module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«66».New.«66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 330

The eta expression is `η(z)^(-1) η(2z) η(3z)^3 η(6z)^(-1) η(11z)^(-1) η(22z) η(33z)^3 η(66z)^(-1)`; see
[the local level table](../../TABLE.md#level-330).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^3 η(6z)^(-1) η(11z)^(-1) η(22z) η(33z)^3 η(66z)^(-1)` at level 330. -/
abbrev cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_330_1 : gamma0CuspForms 330 :=
  gamma0RescaleToLevel cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_330_1_eq_eta :
    cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_330_1 =
      etaQuotientCuspForm 330 sparse![330; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 10 => -1, 21 => 1, 32 => 3, 65 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_330_1_first_coeffs :
    first_coeffs 100 cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_330_1 =
    [0, 0, 1, 1, 1, -1, -1, 0, -1, 0, -2, 0, -1, 0, 2, 0, -1, 0, 1, 0,
     -2, -2, 1, -1, 3, 3, 0, -2, 2, 2, 0, -3, -1, 1, -2, 2, 1, -1, 0, 4,
     0, 2, -2, 2, 1, -1, 4, -2, -1, 0, 1, -2, 0, 2, 1, -1, -2, 0, -2, -1,
     0, -4, -6, 0, 3, -4, -1, -1, -2, -2, -4, 1, -1, -2, 4, -1, 0, 0, 0, 4,
     4, 3, -2, 2, -2, 2, 0, 2, -1, -1, -2, 0, 4, 4, 6, 0, 3, 1, 5, 0] := by
  eta_coeff

end WeightTwoCusps
