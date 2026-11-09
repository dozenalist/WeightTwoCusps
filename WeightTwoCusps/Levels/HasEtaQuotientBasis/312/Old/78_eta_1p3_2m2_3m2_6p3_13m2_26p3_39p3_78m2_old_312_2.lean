module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(2z)^3 η(4z)^(-2) η(6z)^(-2) η(12z)^3 η(26z)^(-2) η(52z)^3 η(78z)^3 η(156z)^(-2)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^3 η(4z)^(-2) η(6z)^(-2) η(12z)^3 η(26z)^(-2) η(52z)^3 η(78z)^3 η(156z)^(-2)` at level 312. -/
abbrev cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_312_2 : gamma0CuspForms 312 :=
  gamma0RescaleToLevel cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_312_2_eq_eta :
    cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_312_2 =
      etaQuotientCuspForm 312 sparse![312; 1 => 3, 3 => -2, 5 => -2, 11 => 3, 25 => -2, 51 => 3, 77 => 3, 155 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_312_2_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_312_2 =
    [0, 0, 1, 0, -3, 0, 2, 0, 1, 0, -1, 0, -1, 0, 3, 0, -1, 0, 0, 0,
     -2, 0, -2, 0, 2, 0, 0, 0, 2, 0, -5, 0, 7, 0, 2, 0, -4, 0, -4, 0,
     7, 0, -3, 0, 0, 0, -2, 0, -3, 0, 3, 0, 0, 0, -1, 0, -5, 0, 8, 0,
     5, 0, -6, 0, -3, 0, 8, 0, -3, 0, 2, 0, 0, 0, -5, 0, 2, 0, 0, 0,
     -6, 0, -2, 0, 1, 0, 6, 0, -2, 0, 0, 0, 6, 0, -1, 0, 4, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
