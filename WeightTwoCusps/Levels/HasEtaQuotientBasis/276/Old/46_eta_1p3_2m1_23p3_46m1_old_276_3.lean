module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«46».New.«46_eta_1p3_2m1_23p3_46m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(3z)^3 η(6z)^(-1) η(69z)^3 η(138z)^(-1)`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_46_eta_1p3_2m1_23p3_46m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^3 η(6z)^(-1) η(69z)^3 η(138z)^(-1)` at level 276. -/
abbrev cuspForm_46_eta_1p3_2m1_23p3_46m1_old_276_3 : gamma0CuspForms 276 :=
  gamma0RescaleToLevel cuspForm_46_eta_1p3_2m1_23p3_46m1 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_46_eta_1p3_2m1_23p3_46m1_old_276_3_eq_eta :
    cuspForm_46_eta_1p3_2m1_23p3_46m1_old_276_3 =
      etaQuotientCuspForm 276 sparse![276; 2 => 3, 5 => -1, 68 => 3, 137 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_46_eta_1p3_2m1_23p3_46m1_old_276_3_first_coeffs :
    first_coeffs 100 cuspForm_46_eta_1p3_2m1_23p3_46m1_old_276_3 =
    [0, 0, 0, 1, 0, 0, -3, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, -1, 0,
     0, -4, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, -1,
     0, 0, 2, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0,
     -2, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, -3, 0, 0, 11, 0, 0, -5, 0,
     0, -1, 0, 0, -6, 0, 0, 1, 0, 0, 12, 0, 0, -3, 0, 0, 2, 0, 0, -2] := by
  eta_coeff

end WeightTwoCusps
