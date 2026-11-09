module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«243».New.«243_eta_3m1_9p5_27m1_81p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(3z)^(-1) η(9z)^5 η(27z)^(-1) η(81z)`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_243_eta_3m1_9p5_27m1_81p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(9z)^5 η(27z)^(-1) η(81z)` at level 486. -/
abbrev cuspForm_243_eta_3m1_9p5_27m1_81p1_old_486_1 : gamma0CuspForms 486 :=
  gamma0RescaleToLevel cuspForm_243_eta_3m1_9p5_27m1_81p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_243_eta_3m1_9p5_27m1_81p1_old_486_1_eq_eta :
    cuspForm_243_eta_3m1_9p5_27m1_81p1_old_486_1 =
      etaQuotientCuspForm 486 sparse![486; 2 => -1, 8 => 5, 26 => -1, 80 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_243_eta_3m1_9p5_27m1_81p1_old_486_1_first_coeffs :
    first_coeffs 100 cuspForm_243_eta_3m1_9p5_27m1_81p1_old_486_1 =
    [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0, 0, -3,
     0, 0, 1, 0, 0, -5, 0, 0, -3, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0,
     -5, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0,
     0, 4, 0, 0, 0, 0, 0, 4, 0, 0, -2, 0, 0, -3, 0, 0, 2, 0, 0, 1,
     0, 0, -1, 0, 0, -3, 0, 0, -7, 0, 0, 1, 0, 0, -2, 0, 0, 4, 0, 0] := by
  eta_coeff

end WeightTwoCusps
