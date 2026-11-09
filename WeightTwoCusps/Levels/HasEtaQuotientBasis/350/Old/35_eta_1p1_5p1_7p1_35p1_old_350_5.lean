module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_1p1_5p1_7p1_35p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(5z) η(25z) η(35z) η(175z)`; see
[the local level table](../../TABLE.md#level-350).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_35_eta_1p1_5p1_7p1_35p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z) η(25z) η(35z) η(175z)` at level 350. -/
abbrev cuspForm_35_eta_1p1_5p1_7p1_35p1_old_350_5 : gamma0CuspForms 350 :=
  gamma0RescaleToLevel cuspForm_35_eta_1p1_5p1_7p1_35p1 5 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_old_350_5_eq_eta :
    cuspForm_35_eta_1p1_5p1_7p1_35p1_old_350_5 =
      etaQuotientCuspForm 350 sparse![350; 4 => 1, 24 => 1, 34 => 1, 174 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_old_350_5_first_coeffs :
    first_coeffs 100 cuspForm_35_eta_1p1_5p1_7p1_35p1_old_350_5 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     -3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
