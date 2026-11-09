module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«225».New.«225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z) η(3z)^(-1) η(5z)^(-1) η(9z) η(15z)^4 η(25z) η(45z)^(-1) η(75z)^(-1) η(225z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(3z)^(-1) η(5z)^(-1) η(9z) η(15z)^4 η(25z) η(45z)^(-1) η(75z)^(-1) η(225z)` at level 450. -/
abbrev cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_old_450_1 : gamma0CuspForms 450 :=
  gamma0RescaleToLevel cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_old_450_1_eq_eta :
    cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_old_450_1 =
      etaQuotientCuspForm 450 sparse![450; 0 => 1, 2 => -1, 4 => -1, 8 => 1, 14 => 4, 24 => 1, 44 => -1, 74 => -1, 224 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_old_450_1_first_coeffs :
    first_coeffs 100 cuspForm_225_eta_1p1_3m1_5m1_9p1_15p4_25p1_45m1_75m1_225p1_old_450_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1, -1, 1, 1, -2, 0, 1, 1, 0,
     0, -1, -2, 1, 2, 1, -1, 0, 0, -1, 2, 0, -3, -2, 0, 0, 0, 5, -3, -1,
     3, -2, 2, -2, -2, 2, 0, 3, 1, 0, 0, 2, -1, -4, 0, -4, 0, 3, -1, 3,
     2, 0, -1, -1, 0, 0, 4, -6, 0, 2, 0, 4, -1, -5, -4, -2, 0, -1, 0, 0,
     0, -1, 5, 5, -2, 2, 1, -4, 6, 2, -2, 0, 2, 1, 0, 0, -6, -1, 3, 2] := by
  eta_coeff

end WeightTwoCusps
