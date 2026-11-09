module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«69».New.«69_eta_1p1_3p1_23p1_69p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(2z) η(6z) η(46z) η(138z)`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_69_eta_1p1_3p1_23p1_69p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(6z) η(46z) η(138z)` at level 276. -/
abbrev cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_2 : gamma0CuspForms 276 :=
  gamma0RescaleToLevel cuspForm_69_eta_1p1_3p1_23p1_69p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_2_eq_eta :
    cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_2 =
      etaQuotientCuspForm 276 sparse![276; 1 => 1, 5 => 1, 45 => 1, 137 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_2_first_coeffs :
    first_coeffs 100 cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 2, 0,
     -1, 0, 2, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0,
     -1, 0, -1, 0, 2, 0, 0, 0, 1, 0, 2, 0, 1, 0, -2, 0, 1, 0, 0, 0,
     3, 0, -2, 0, -2, 0, 0, 0, -3, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0,
     -1, 0, 2, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
