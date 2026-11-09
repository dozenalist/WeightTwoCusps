module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«156».New.«156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(2z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(24z) η(26z)^(-1) η(78z)^2 η(104z) η(156z) η(312z)^(-1)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(24z) η(26z)^(-1) η(78z)^2 η(104z) η(156z) η(312z)^(-1)` at level 312. -/
abbrev cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1_old_312_2 : gamma0CuspForms 312 :=
  gamma0Rescale cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1_old_312_2_eq_eta :
    cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1_old_312_2 =
      etaQuotientCuspForm 312 sparse![312; 1 => 2, 3 => 1, 5 => -1, 7 => -1, 23 => 1, 25 => -1, 77 => 2, 103 => 1, 155 => 1, 311 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1_old_312_2_first_coeffs :
    first_coeffs 100 cuspForm_156_eta_1p2_2p1_3m1_4m1_12p1_13m1_39p2_52p1_78p1_156m1_old_312_2 =
    [0, 0, 0, 0, 1, 0, -2, 0, -2, 0, 5, 0, 0, 0, -2, 0, 2, 0, -2, 0,
     -2, 0, 1, 0, -2, 0, 0, 0, 6, 0, -1, 0, -2, 0, 0, 0, 3, 0, -2, 0,
     -1, 0, 2, 0, -4, 0, 4, 0, -1, 0, -6, 0, 0, 0, 6, 0, -2, 0, -2, 0,
     -4, 0, 8, 0, 7, 0, -5, 0, 4, 0, -4, 0, 0, 0, -2, 0, -6, 0, 0, 0,
     10, 0, -5, 0, -4, 0, -2, 0, 3, 0, 3, 0, -2, 0, 5, 0, -4, 0, 6, 0] := by
  eta_coeff

end WeightTwoCusps
