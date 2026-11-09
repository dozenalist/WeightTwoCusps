module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«138».New.«138_eta_1p1_2m1_3m2_6p4_23p1_46m1_69m2_138p4»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(2z) η(4z)^(-1) η(6z)^(-2) η(12z)^4 η(46z) η(92z)^(-1) η(138z)^(-2) η(276z)^4`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_138_eta_1p1_2m1_3m2_6p4_23p1_46m1_69m2_138p4`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z)^(-1) η(6z)^(-2) η(12z)^4 η(46z) η(92z)^(-1) η(138z)^(-2) η(276z)^4` at level 276. -/
abbrev cuspForm_138_eta_1p1_2m1_3m2_6p4_23p1_46m1_69m2_138p4_old_276_2 : gamma0CuspForms 276 :=
  gamma0Rescale cuspForm_138_eta_1p1_2m1_3m2_6p4_23p1_46m1_69m2_138p4 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_138_eta_1p1_2m1_3m2_6p4_23p1_46m1_69m2_138p4_old_276_2_eq_eta :
    cuspForm_138_eta_1p1_2m1_3m2_6p4_23p1_46m1_69m2_138p4_old_276_2 =
      etaQuotientCuspForm 276 sparse![276; 1 => 1, 3 => -1, 5 => -2, 11 => 4, 45 => 1, 91 => -1, 137 => -2, 275 => 4] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_138_eta_1p1_2m1_3m2_6p4_23p1_46m1_69m2_138p4_old_276_2_first_coeffs :
    first_coeffs 100 cuspForm_138_eta_1p1_2m1_3m2_6p4_23p1_46m1_69m2_138p4_old_276_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
     1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0,
     0, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     -2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1, 0] := by
  eta_coeff

end WeightTwoCusps
