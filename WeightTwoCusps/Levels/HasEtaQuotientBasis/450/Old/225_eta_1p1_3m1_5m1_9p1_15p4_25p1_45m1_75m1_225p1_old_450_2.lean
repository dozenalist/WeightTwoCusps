module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«225».New.«225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(2z) η(6z)^(-1) η(10z)^(-1) η(18z) η(30z)^4 η(50z) η(90z)^(-1) η(150z)^(-1) η(450z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(6z)^(-1) η(10z)^(-1) η(18z) η(30z)^4 η(50z) η(90z)^(-1) η(150z)^(-1) η(450z)` at level 450. -/
abbrev cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_old_450_2 : gamma0CuspForms 450 :=
  gamma0Rescale cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_old_450_2_eq_eta :
    cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_old_450_2 =
      etaQuotientCuspForm 450 sparse![450; 1 => 1, 5 => -1, 9 => -1, 17 => 1, 29 => 4, 49 => 1, 89 => -1, 149 => -1, 449 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_old_450_2_first_coeffs :
    first_coeffs 100 cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_old_450_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0,
     -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -2, 0, 0, 0, 1, 0, 1, 0, 0, 0,
     0, 0, -1, 0, -2, 0, 1, 0, 2, 0, 1, 0, -1, 0, 0, 0, 0, 0, -1, 0,
     2, 0, 0, 0, -3, 0, -2, 0, 0, 0, 0, 0, 0, 0, 5, 0, -3, 0, -1, 0,
     3, 0, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 0, 0, 3, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
