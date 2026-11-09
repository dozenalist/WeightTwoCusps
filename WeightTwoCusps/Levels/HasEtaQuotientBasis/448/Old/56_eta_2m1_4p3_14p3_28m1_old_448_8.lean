module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_2m1_4p3_14p3_28m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(16z)^(-1) η(32z)^3 η(112z)^3 η(224z)^(-1)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(8z)` of `cuspForm_56_eta_2m1_4p3_14p3_28m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(16z)^(-1) η(32z)^3 η(112z)^3 η(224z)^(-1)` at level 448. -/
abbrev cuspForm_56_eta_2m1_4p3_14p3_28m1_old_448_8 : gamma0CuspForms 448 :=
  gamma0Rescale cuspForm_56_eta_2m1_4p3_14p3_28m1 8

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_2m1_4p3_14p3_28m1_old_448_8_eq_eta :
    cuspForm_56_eta_2m1_4p3_14p3_28m1_old_448_8 =
      etaQuotientCuspForm 448 sparse![448; 15 => -1, 31 => 3, 111 => 3, 223 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_2m1_4p3_14p3_28m1_old_448_8_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_2m1_4p3_14p3_28m1_old_448_8 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
