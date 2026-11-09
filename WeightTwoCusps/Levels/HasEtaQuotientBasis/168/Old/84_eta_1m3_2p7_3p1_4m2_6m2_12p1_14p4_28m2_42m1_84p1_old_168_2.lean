module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».New.«84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 168

The eta expression is `η(2z)^(-3) η(4z)^7 η(6z) η(8z)^(-2) η(12z)^(-2) η(24z) η(28z)^4 η(56z)^(-2) η(84z)^(-1) η(168z)`; see
[the local level table](../../TABLE.md#level-168).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^7 η(6z) η(8z)^(-2) η(12z)^(-2) η(24z) η(28z)^4 η(56z)^(-2) η(84z)^(-1) η(168z)` at level 168. -/
abbrev cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_old_168_2 : gamma0CuspForms 168 :=
  gamma0Rescale cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_old_168_2_eq_eta :
    cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_old_168_2 =
      etaQuotientCuspForm 168 sparse![168; 1 => -3, 3 => 7, 5 => 1, 7 => -2, 11 => -2, 23 => 1, 27 => 4, 55 => -2, 83 => -1, 167 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_old_168_2_first_coeffs :
    first_coeffs 100 cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_old_168_2 =
    [0, 0, 0, 0, 1, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 3, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 1, 0, -3, 0, -4, 0, -12, 0, -8, 0, 0, 0,
     -6, 0, 0, 0, -6, 0, -12, 0, 1, 0, 0, 0, 2, 0, -3, 0, -4, 0, 12, 0,
     3, 0, 12, 0, 7, 0, -6, 0, 12, 0, 0, 0, 11, 0, 12, 0, -4, 0, 3, 0,
     0, 0, 12, 0, 4, 0, -12, 0, 6, 0, 0, 0, 6, 0, 24, 0, -7, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
