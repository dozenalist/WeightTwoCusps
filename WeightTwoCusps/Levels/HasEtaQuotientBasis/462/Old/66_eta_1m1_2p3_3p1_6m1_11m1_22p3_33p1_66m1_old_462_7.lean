module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«66».New.«66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(7z)^(-1) η(14z)^3 η(21z) η(42z)^(-1) η(77z)^(-1) η(154z)^3 η(231z) η(462z)^(-1)`; see
[the local level table](../../TABLE.md#level-462).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(7z)^(-1) η(14z)^3 η(21z) η(42z)^(-1) η(77z)^(-1) η(154z)^3 η(231z) η(462z)^(-1)` at level 462. -/
abbrev cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_old_462_7 : gamma0CuspForms 462 :=
  gamma0Rescale cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1 7

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_old_462_7_eq_eta :
    cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_old_462_7 =
      etaQuotientCuspForm 462 sparse![462; 6 => -1, 13 => 3, 20 => 1, 41 => -1, 76 => -1, 153 => 3, 230 => 1, 461 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_old_462_7_first_coeffs :
    first_coeffs 100 cuspForm_66_eta_1m1_2p3_3p1_6m1_11m1_22p3_33p1_66m1_old_462_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 1, 0, 0,
     0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
