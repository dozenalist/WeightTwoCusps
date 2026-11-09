module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_1p1_5p1_7p1_35p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(8z) η(40z) η(56z) η(280z)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(8z)` of `cuspForm_35_eta_1p1_5p1_7p1_35p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z) η(40z) η(56z) η(280z)` at level 280. -/
abbrev cuspForm_35_eta_1p1_5p1_7p1_35p1_old_280_8 : gamma0CuspForms 280 :=
  gamma0Rescale cuspForm_35_eta_1p1_5p1_7p1_35p1 8

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_old_280_8_eq_eta :
    cuspForm_35_eta_1p1_5p1_7p1_35p1_old_280_8 =
      etaQuotientCuspForm 280 sparse![280; 7 => 1, 39 => 1, 55 => 1, 279 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_old_280_8_first_coeffs :
    first_coeffs 100 cuspForm_35_eta_1p1_5p1_7p1_35p1_old_280_8 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
