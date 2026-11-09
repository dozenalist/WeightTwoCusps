module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«66».New.«66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(6z)^(-1) η(12z) η(18z)^3 η(36z)^(-1) η(66z)^(-1) η(132z) η(198z)^3 η(396z)^(-1)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-1) η(12z) η(18z)^3 η(36z)^(-1) η(66z)^(-1) η(132z) η(198z)^3 η(396z)^(-1)` at level 396. -/
abbrev cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_396_6 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_396_6_eq_eta :
    cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_396_6 =
      etaQuotientCuspForm 396 sparse![396; 5 => -1, 11 => 1, 17 => 3, 35 => -1, 65 => -1, 131 => 1, 197 => 3, 395 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_396_6_first_coeffs :
    first_coeffs 100 cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_396_6 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
