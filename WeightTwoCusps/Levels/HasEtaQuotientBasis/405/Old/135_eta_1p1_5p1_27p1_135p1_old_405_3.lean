module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_1p1_5p1_27p1_135p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 405

The eta expression is `η(3z) η(15z) η(81z) η(405z)`; see
[the local level table](../../TABLE.md#level-405).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_135_eta_1p1_5p1_27p1_135p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(15z) η(81z) η(405z)` at level 405. -/
abbrev cuspForm_135_eta_1p1_5p1_27p1_135p1_old_405_3 : gamma0CuspForms 405 :=
  gamma0Rescale cuspForm_135_eta_1p1_5p1_27p1_135p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_135_eta_1p1_5p1_27p1_135p1_old_405_3_eq_eta :
    cuspForm_135_eta_1p1_5p1_27p1_135p1_old_405_3 =
      etaQuotientCuspForm 405 sparse![405; 2 => 1, 14 => 1, 80 => 1, 404 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_135_eta_1p1_5p1_27p1_135p1_old_405_3_first_coeffs :
    first_coeffs 100 cuspForm_135_eta_1p1_5p1_27p1_135p1_old_405_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, -1, 0, 0,
     0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
