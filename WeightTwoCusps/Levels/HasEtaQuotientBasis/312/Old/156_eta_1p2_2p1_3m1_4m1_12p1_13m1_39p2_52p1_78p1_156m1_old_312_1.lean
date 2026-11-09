module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«156».New.«156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(z)^2 η(2z) η(3z)^(-1) η(4z)^(-1) η(12z) η(13z)^(-1) η(39z)^2 η(52z) η(78z) η(156z)^(-1)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(2z) η(3z)^(-1) η(4z)^(-1) η(12z) η(13z)^(-1) η(39z)^2 η(52z) η(78z) η(156z)^(-1)` at level 312. -/
abbrev cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1_old_312_1 : gamma0CuspForms 312 :=
  gamma0RescaleToLevel cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1_old_312_1_eq_eta :
    cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1_old_312_1 =
      etaQuotientCuspForm 312 sparse![312; 0 => 2, 1 => 1, 2 => -1, 3 => -1, 11 => 1, 12 => -1, 38 => 2, 51 => 1, 77 => 1, 155 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1_old_312_1_first_coeffs :
    first_coeffs 100 cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1_old_312_1 =
    [0, 0, 1, -2, -2, 5, 0, -2, 2, -2, -2, 1, -2, 0, 6, -1, -2, 0, 3, -2,
     -1, 2, -4, 4, -1, -6, 0, 6, -2, -2, -4, 8, 7, -5, 4, -4, 0, -2, -6, 0,
     10, -5, -4, -2, 3, 3, -2, 5, -4, 6, 1, -8, 0, 6, -6, -4, -8, 8, 10, 3,
     5, -4, -4, 0, -6, 1, 10, -8, -4, -8, 6, -3, 4, 6, -6, 0, 6, -6, 1, 12,
     -9, 4, -8, -3, 2, 14, 4, -6, 0, -3, -4, 2, 4, -10, 2, -10, 6, 6, 1, 5] := by
  eta_coeff

end WeightTwoCusps
