module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«138».New.«138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z) η(2z)^(-1) η(3z)^(-1) η(6z)^3 η(23z) η(46z)^(-1) η(69z)^(-1) η(138z)^3`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(3z)^(-1) η(6z)^3 η(23z) η(46z)^(-1) η(69z)^(-1) η(138z)^3` at level 276. -/
abbrev cuspForm_138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3_old_276_1 : gamma0CuspForms 276 :=
  gamma0RescaleToLevel cuspForm_138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3_old_276_1_eq_eta :
    cuspForm_138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3_old_276_1 =
      etaQuotientCuspForm 276 sparse![276; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 22 => 1, 45 => -1, 68 => -1, 137 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3_old_276_1_first_coeffs :
    first_coeffs 100 cuspForm_138_eta_1p1_2m1_3m1_6p3_23p1_46m1_69m1_138p3_old_276_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, -1,
     -1, 1, 1, 0, 0, 1, -1, 1, -1, 0, 1, 1, 0, 0, -1, -1, -1, -1, 1, 0,
     0, 1, 0, 1, 0, -2, 0, 0, -1, 0, -1, 1, 1, 0, 0, 0, 1, 0, 1, 2,
     0, -1, 0, 0, 0, 0, -1, -1, 1, 0, 1, 0, 2, 0, 0, -1, -2, -3, 0, -2,
     1, 0, -2, 0, 2, 1, -1, 0, 1, 0, 0, 2, 0, -1, -1, -1, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
