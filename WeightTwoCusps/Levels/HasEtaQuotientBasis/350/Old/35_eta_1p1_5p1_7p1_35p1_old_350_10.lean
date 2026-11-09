module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_1p1_5p1_7p1_35p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(10z) η(50z) η(70z) η(350z)`; see
[the local level table](../../TABLE.md#level-350).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(10z)` of `cuspForm_35_eta_1p1_5p1_7p1_35p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(10z) η(50z) η(70z) η(350z)` at level 350. -/
abbrev cuspForm_35_eta_1p1_5p1_7p1_35p1_old_350_10 : gamma0CuspForms 350 :=
  gamma0Rescale cuspForm_35_eta_1p1_5p1_7p1_35p1 10

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_old_350_10_eq_eta :
    cuspForm_35_eta_1p1_5p1_7p1_35p1_old_350_10 =
      etaQuotientCuspForm 350 sparse![350; 9 => 1, 49 => 1, 69 => 1, 349 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_old_350_10_first_coeffs :
    first_coeffs 100 cuspForm_35_eta_1p1_5p1_7p1_35p1_old_350_10 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
