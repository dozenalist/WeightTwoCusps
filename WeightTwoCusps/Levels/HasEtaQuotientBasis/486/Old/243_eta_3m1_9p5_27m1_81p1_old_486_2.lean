module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«243».New.«243_eta_3m1_9p5_27m1_81p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(6z)^(-1) η(18z)^5 η(54z)^(-1) η(162z)`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_243_eta_3m1_9p5_27m1_81p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-1) η(18z)^5 η(54z)^(-1) η(162z)` at level 486. -/
abbrev cuspForm_243_eta_3m1_9p5_27m1_81p1_old_486_2 : gamma0CuspForms 486 :=
  gamma0Rescale cuspForm_243_eta_3m1_9p5_27m1_81p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_243_eta_3m1_9p5_27m1_81p1_old_486_2_eq_eta :
    cuspForm_243_eta_3m1_9p5_27m1_81p1_old_486_2 =
      etaQuotientCuspForm 486 sparse![486; 5 => -1, 17 => 5, 53 => -1, 161 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_243_eta_3m1_9p5_27m1_81p1_old_486_2_first_coeffs :
    first_coeffs 100 cuspForm_243_eta_3m1_9p5_27m1_81p1_old_486_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, -3, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0,
     -5, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
