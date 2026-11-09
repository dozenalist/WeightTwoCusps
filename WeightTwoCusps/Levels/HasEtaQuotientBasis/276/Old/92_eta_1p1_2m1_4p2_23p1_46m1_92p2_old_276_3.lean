module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«92».New.«92_eta_1p1_2m1_4p2_23p1_46m1_92p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(3z) η(6z)^(-1) η(12z)^2 η(69z) η(138z)^(-1) η(276z)^2`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_92_eta_1p1_2m1_4p2_23p1_46m1_92p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(6z)^(-1) η(12z)^2 η(69z) η(138z)^(-1) η(276z)^2` at level 276. -/
abbrev cuspForm_92_eta_1p1_2m1_4p2_23p1_46m1_92p2_old_276_3 : gamma0CuspForms 276 :=
  gamma0Rescale cuspForm_92_eta_1p1_2m1_4p2_23p1_46m1_92p2 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_92_eta_1p1_2m1_4p2_23p1_46m1_92p2_old_276_3_eq_eta :
    cuspForm_92_eta_1p1_2m1_4p2_23p1_46m1_92p2_old_276_3 =
      etaQuotientCuspForm 276 sparse![276; 2 => 1, 5 => -1, 11 => 2, 68 => 1, 137 => -1, 275 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_92_eta_1p1_2m1_4p2_23p1_46m1_92p2_old_276_3_first_coeffs :
    first_coeffs 100 cuspForm_92_eta_1p1_2m1_4p2_23p1_46m1_92p2_old_276_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 1,
     0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0,
     0, 1, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
