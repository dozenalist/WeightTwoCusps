module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«140».New.«140_eta_1p1_7p1_20p1_140p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(2z) η(14z) η(40z) η(280z)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_140_eta_1p1_7p1_20p1_140p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(14z) η(40z) η(280z)` at level 280. -/
abbrev cuspForm_140_eta_1p1_7p1_20p1_140p1_old_280_2 : gamma0CuspForms 280 :=
  gamma0Rescale cuspForm_140_eta_1p1_7p1_20p1_140p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_140_eta_1p1_7p1_20p1_140p1_old_280_2_eq_eta :
    cuspForm_140_eta_1p1_7p1_20p1_140p1_old_280_2 =
      etaQuotientCuspForm 280 sparse![280; 1 => 1, 13 => 1, 39 => 1, 279 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_140_eta_1p1_7p1_20p1_140p1_old_280_2_first_coeffs :
    first_coeffs 100 cuspForm_140_eta_1p1_7p1_20p1_140p1_old_280_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -2, 0,
     0, 0, -2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 3, 0,
     0, 0, 0, 0, -1, 0, 2, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 2, 0,
     -1, 0, 2, 0, 0, 0, -3, 0, -1, 0, 0, 0, 0, 0, -2, 0, 2, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
