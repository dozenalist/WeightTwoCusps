module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«66».New.«66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(z)^(-1) η(2z)^3 η(3z) η(6z)^(-1) η(11z)^(-1) η(22z)^3 η(33z) η(66z)^(-1)`; see
[the local level table](../../TABLE.md#level-462).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(3z) η(6z)^(-1) η(11z)^(-1) η(22z)^3 η(33z) η(66z)^(-1)` at level 462. -/
abbrev cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_old_462_1 : gamma0CuspForms 462 :=
  gamma0RescaleToLevel cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_old_462_1_eq_eta :
    cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_old_462_1 =
      etaQuotientCuspForm 462 sparse![462; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 10 => -1, 21 => 3, 32 => 1, 65 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_old_462_1_first_coeffs :
    first_coeffs 100 cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_old_462_1 =
    [0, 1, 1, -1, -1, -2, -1, 1, 0, 1, -2, 1, 4, 1, 1, -1, -1, -2, 1, 0,
     -1, -1, 1, 2, -3, 2, 1, 2, -1, 0, -1, -5, 2, -1, -2, -2, -1, 3, 0, -1,
     3, -2, -1, 0, -1, -2, 2, 5, 4, 3, 2, 2, -1, 3, 2, -2, -9, 0, 0, -1,
     1, 3, -5, 1, 7, -2, -1, -7, 2, -5, -2, 0, 0, -8, 3, 7, 0, 1, -1, -1,
     -1, -2, -2, 6, -5, 4, 0, 6, 0, 3, -2, -8, -5, -4, 5, 0, 1, -1, 3, 1] := by
  eta_coeff

end WeightTwoCusps
