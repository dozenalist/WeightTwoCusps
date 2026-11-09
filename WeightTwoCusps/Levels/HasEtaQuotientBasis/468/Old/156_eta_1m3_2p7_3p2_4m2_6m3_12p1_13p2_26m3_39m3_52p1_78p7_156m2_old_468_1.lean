module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«156».New.«156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-2) η(6z)^(-3) η(12z) η(13z)^2 η(26z)^(-3) η(39z)^(-3) η(52z) η(78z)^7 η(156z)^(-2)`; see
[the local level table](../../TABLE.md#level-468).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-2) η(6z)^(-3) η(12z) η(13z)^2 η(26z)^(-3) η(39z)^(-3) η(52z) η(78z)^7 η(156z)^(-2)` at level 468. -/
abbrev cuspForm_156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2_old_468_1 : gamma0CuspForms 468 :=
  gamma0RescaleToLevel cuspForm_156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2_old_468_1_eq_eta :
    cuspForm_156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2_old_468_1 =
      etaQuotientCuspForm 468 sparse![468; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 11 => 1, 12 => 2, 25 => -3, 38 => -3, 51 => 1, 77 => 7, 155 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2_old_468_1_first_coeffs :
    first_coeffs 100 cuspForm_156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2_old_468_1 =
    [0, 0, 0, 0, 0, 1, 3, 2, -1, -2, -2, 1, 2, 0, -2, -7, -2, 2, -2, -4,
     -7, 0, 2, 4, 4, -4, -1, 2, 14, 6, -2, 6, 2, 7, 0, 2, -2, -8, 4, 2,
     -2, -11, 2, 0, -11, -1, -2, 3, -6, 0, 4, -8, -2, 2, 3, -12, 0, 10, 0, -1,
     -3, 8, -2, 4, 8, 1, 0, 2, 14, -8, -8, -5, -3, 2, -2, 6, -12, -6, 0, 4,
     13, -2, 10, 5, 0, 12, 2, -2, -2, -1, 0, 2, -4, -12, -10, -14, -3, 2, -6, 5] := by
  eta_coeff

end WeightTwoCusps
