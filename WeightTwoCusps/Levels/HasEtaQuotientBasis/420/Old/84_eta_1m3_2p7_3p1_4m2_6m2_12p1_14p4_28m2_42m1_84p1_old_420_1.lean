module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».New.«84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(12z) η(14z)^4 η(28z)^(-2) η(42z)^(-1) η(84z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(12z) η(14z)^4 η(28z)^(-2) η(42z)^(-1) η(84z)` at level 420. -/
abbrev cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_old_420_1_eq_eta :
    cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 13 => 4, 27 => -2, 41 => -1, 83 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_old_420_1 =
    [0, 0, 1, 3, 2, 0, 1, 0, 1, 3, 0, 0, -1, 0, 1, -3, -4, -12, -8, 0,
     -6, 0, -6, -12, 1, 0, 2, -3, -4, 12, 3, 12, 7, -6, 12, 0, 11, 12, -4, 3,
     0, 12, 4, -12, 6, 0, 6, 24, -7, 0, -5, 0, 4, -12, 7, -12, 1, -3, -6, 12,
     -3, -24, -4, 3, 2, 12, 0, 12, -18, 0, 0, 0, -8, -24, -10, -9, 4, -12, -13, -24,
     6, 6, 0, -12, -4, 12, 8, 0, -6, 12, 0, 12, 6, 6, -12, -12, 7, 24, 1, 0] := by
  eta_coeff

end WeightTwoCusps
