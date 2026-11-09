module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«132».New.«132_eta_1m3_2p8_3p1_4m3_6m2_11m1_12p1_22p1_33p3_66m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-2) η(11z)^(-1) η(12z) η(22z) η(33z)^3 η(66z)^(-1)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_132_eta_1m3_2p8_3p1_4m3_6m2_11m1_12p1_22p1_33p3_66m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-2) η(11z)^(-1) η(12z) η(22z) η(33z)^3 η(66z)^(-1)` at level 396. -/
abbrev cuspForm_132_eta_1m3_2p8_3p1_4m3_6m2_11m1_12p1_22p1_33p3_66m1_old_396_1 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_132_eta_1m3_2p8_3p1_4m3_6m2_11m1_12p1_22p1_33p3_66m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_132_eta_1m3_2p8_3p1_4m3_6m2_11m1_12p1_22p1_33p3_66m1_old_396_1_eq_eta :
    cuspForm_132_eta_1m3_2p8_3p1_4m3_6m2_11m1_12p1_22p1_33p3_66m1_old_396_1 =
      etaQuotientCuspForm 396 sparse![396; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -2, 10 => -1, 11 => 1, 21 => 1, 32 => 3, 65 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m3_2p8_3p1_4m3_6m2_11m1_12p1_22p1_33p3_66m1_old_396_1_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m3_2p8_3p1_4m3_6m2_11m1_12p1_22p1_33p3_66m1_old_396_1 =
    [0, 0, 1, 3, 1, -3, -1, 0, -1, 0, -2, 0, -1, -2, 4, -2, -3, 2, 1, 2,
     -2, -2, 1, -1, 1, 7, -2, -6, 4, 4, 2, -5, -1, 1, -2, 2, 1, -1, 0, 6,
     2, 4, -4, 0, 1, -3, 8, -4, 3, 0, -1, 0, -2, 0, -1, -1, -4, 6, -6, 1,
     2, -6, -8, 0, 5, -8, -1, -3, -2, -8, -8, 5, -1, -6, 6, 1, 0, 0, 2, 8,
     6, 3, -2, 2, -4, 2, 0, 4, -1, -1, -2, -4, 8, 12, 8, -4, 1, 1, 9, 0] := by
  eta_coeff

end WeightTwoCusps
