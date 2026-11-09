module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«66».New.«66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(3z)^(-1) η(6z) η(9z)^3 η(18z)^(-1) η(33z)^(-1) η(66z) η(99z)^3 η(198z)^(-1)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z) η(9z)^3 η(18z)^(-1) η(33z)^(-1) η(66z) η(99z)^3 η(198z)^(-1)` at level 396. -/
abbrev cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_396_3 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_396_3_eq_eta :
    cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_396_3 =
      etaQuotientCuspForm 396 sparse![396; 2 => -1, 5 => 1, 8 => 3, 17 => -1, 32 => -1, 65 => 1, 98 => 3, 197 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_396_3_first_coeffs :
    first_coeffs 100 cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_396_3 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     -2, 0, 0, -2, 0, 0, 1, 0, 0, -1, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0,
     0, -2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, -3, 0, 0, -1, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
