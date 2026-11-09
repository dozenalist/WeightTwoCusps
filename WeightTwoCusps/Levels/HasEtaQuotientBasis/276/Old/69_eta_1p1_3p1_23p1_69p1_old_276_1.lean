module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«69».New.«69_eta_1p1_3p1_23p1_69p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z) η(3z) η(23z) η(69z)`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_69_eta_1p1_3p1_23p1_69p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(3z) η(23z) η(69z)` at level 276. -/
abbrev cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_1 : gamma0CuspForms 276 :=
  gamma0RescaleToLevel cuspForm_69_eta_1p1_3p1_23p1_69p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_1_eq_eta :
    cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_1 =
      etaQuotientCuspForm 276 sparse![276; 0 => 1, 2 => 1, 22 => 1, 68 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_1_first_coeffs :
    first_coeffs 100 cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_1 =
    [0, 0, 0, 0, 1, -1, -1, -1, 1, 2, -1, 2, 0, 0, -1, -1, -1, -1, 0, 1,
     -1, -1, 2, 0, 1, 2, 1, -2, 1, 0, 3, -2, -2, 0, -3, 0, -1, 0, 1, 0,
     -1, 2, 1, 1, 0, -1, 0, 0, -2, -2, 2, 3, 3, -1, -2, 0, 1, -1, -1, 0,
     1, 2, 1, 3, -2, -4, 0, 1, -3, 0, 0, -4, -1, -2, -2, 2, 1, 4, -4, 3,
     1, 0, 3, 2, 1, 2, 3, 0, -2, 3, 3, -4, 1, -4, -1, 0, 1, -4, -2, -6] := by
  eta_coeff

end WeightTwoCusps
