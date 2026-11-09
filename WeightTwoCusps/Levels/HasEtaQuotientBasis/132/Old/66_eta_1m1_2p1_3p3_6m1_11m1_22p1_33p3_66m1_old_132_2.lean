module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«66».New.«66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 132

The eta expression is `η(2z)^(-1) η(4z) η(6z)^3 η(12z)^(-1) η(22z)^(-1) η(44z) η(66z)^3 η(132z)^(-1)`; see
[the local level table](../../TABLE.md#level-132).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z) η(6z)^3 η(12z)^(-1) η(22z)^(-1) η(44z) η(66z)^3 η(132z)^(-1)` at level 132. -/
abbrev cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_132_2 : gamma0CuspForms 132 :=
  gamma0Rescale cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_132_2_eq_eta :
    cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_132_2 =
      etaQuotientCuspForm 132 sparse![132; 1 => -1, 3 => 1, 5 => 3, 11 => -1, 21 => -1, 43 => 1, 65 => 3, 131 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_132_2_first_coeffs :
    first_coeffs 100 cuspForm_66_eta_1m1_2p1_3p3_6m1_11m1_22p1_33p3_66m1_old_132_2 =
    [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     -2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0,
     -2, 0, -2, 0, 1, 0, -1, 0, 3, 0, 3, 0, 0, 0, -2, 0, 2, 0, 2, 0,
     0, 0, -3, 0, -1, 0, 1, 0, -2, 0, 2, 0, 1, 0, -1, 0, 0, 0, 4, 0,
     0, 0, 2, 0, -2, 0, 2, 0, 1, 0, -1, 0, 4, 0, -2, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
