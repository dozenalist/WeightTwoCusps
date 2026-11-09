module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_2m1_4p3_14p3_28m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(10z)^(-1) η(20z)^3 η(70z)^3 η(140z)^(-1)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_56_eta_2m1_4p3_14p3_28m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(10z)^(-1) η(20z)^3 η(70z)^3 η(140z)^(-1)` at level 280. -/
abbrev cuspForm_56_eta_2m1_4p3_14p3_28m1_old_280_5 : gamma0CuspForms 280 :=
  gamma0Rescale cuspForm_56_eta_2m1_4p3_14p3_28m1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_2m1_4p3_14p3_28m1_old_280_5_eq_eta :
    cuspForm_56_eta_2m1_4p3_14p3_28m1_old_280_5 =
      etaQuotientCuspForm 280 sparse![280; 9 => -1, 19 => 3, 69 => 3, 139 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_2m1_4p3_14p3_28m1_old_280_5_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_2m1_4p3_14p3_28m1_old_280_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
