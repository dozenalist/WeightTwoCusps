module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(4z)^3 η(8z)^(-2) η(12z)^(-2) η(24z)^3 η(52z)^(-2) η(104z)^3 η(156z)^3 η(312z)^(-2)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^3 η(8z)^(-2) η(12z)^(-2) η(24z)^3 η(52z)^(-2) η(104z)^3 η(156z)^3 η(312z)^(-2)` at level 312. -/
abbrev cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_312_4 : gamma0CuspForms 312 :=
  gamma0Rescale cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_312_4_eq_eta :
    cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_312_4 =
      etaQuotientCuspForm 312 sparse![312; 3 => 3, 7 => -2, 11 => -2, 23 => 3, 51 => -2, 103 => 3, 155 => 3, 311 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_312_4_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_312_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, -3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0,
     -1, 0, 0, 0, -1, 0, 0, 0, 3, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, -2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0,
     -5, 0, 0, 0, 7, 0, 0, 0, 2, 0, 0, 0, -4, 0, 0, 0, -4, 0, 0, 0,
     7, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
