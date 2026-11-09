module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(3z)^3 η(6z)^(-2) η(9z)^(-2) η(18z)^3 η(39z)^(-2) η(78z)^3 η(117z)^3 η(234z)^(-2)`; see
[the local level table](../../TABLE.md#level-234).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^3 η(6z)^(-2) η(9z)^(-2) η(18z)^3 η(39z)^(-2) η(78z)^3 η(117z)^3 η(234z)^(-2)` at level 234. -/
abbrev cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_234_3 : gamma0CuspForms 234 :=
  gamma0Rescale cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_234_3_eq_eta :
    cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_234_3 =
      etaQuotientCuspForm 234 sparse![234; 2 => 3, 5 => -2, 8 => -2, 17 => 3, 38 => -2, 77 => 3, 116 => 3, 233 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_234_3_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2_old_234_3 =
    [0, 0, 0, 1, 0, 0, -3, 0, 0, 2, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0,
     0, 3, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 2, 0, 0, 0,
     0, 0, 2, 0, 0, -5, 0, 0, 7, 0, 0, 2, 0, 0, -4, 0, 0, -4, 0, 0,
     7, 0, 0, -3, 0, 0, 0, 0, 0, -2, 0, 0, -3, 0, 0, 3, 0, 0, 0, 0,
     0, -1, 0, 0, -5, 0, 0, 8, 0, 0, 5, 0, 0, -6, 0, 0, -3, 0, 0, 8] := by
  eta_coeff

end WeightTwoCusps
