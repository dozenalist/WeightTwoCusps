module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_1p1_5p1_7p1_35p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 140

The eta expression is `η(4z) η(20z) η(28z) η(140z)`; see
[the local level table](../../TABLE.md#level-140).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_35_eta_1p1_5p1_7p1_35p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(20z) η(28z) η(140z)` at level 140. -/
abbrev cuspForm_35_eta_1p1_5p1_7p1_35p1_old_140_4 : gamma0CuspForms 140 :=
  gamma0Rescale cuspForm_35_eta_1p1_5p1_7p1_35p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_old_140_4_eq_eta :
    cuspForm_35_eta_1p1_5p1_7p1_35p1_old_140_4 =
      etaQuotientCuspForm 140 sparse![140; 3 => 1, 19 => 1, 27 => 1, 139 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_old_140_4_first_coeffs :
    first_coeffs 100 cuspForm_35_eta_1p1_5p1_7p1_35p1_old_140_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
     1, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0,
     -1, 0, 0, 0, -3, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0,
     -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 4, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
