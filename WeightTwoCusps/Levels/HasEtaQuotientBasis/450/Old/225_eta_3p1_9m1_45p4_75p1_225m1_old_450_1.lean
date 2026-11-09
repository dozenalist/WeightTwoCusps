module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«225».New.«225_eta_3p1_9m1_45p4_75p1_225m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(3z) η(9z)^(-1) η(45z)^4 η(75z) η(225z)^(-1)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(9z)^(-1) η(45z)^4 η(75z) η(225z)^(-1)` at level 450. -/
abbrev cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_old_450_1 : gamma0CuspForms 450 :=
  gamma0RescaleToLevel cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_old_450_1_eq_eta :
    cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_old_450_1 =
      etaQuotientCuspForm 450 sparse![450; 2 => 1, 8 => -1, 44 => 4, 74 => 1, 224 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_old_450_1_first_coeffs :
    first_coeffs 100 cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_old_450_1 =
    [0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 2,
     0, 0, -1, 0, 0, -1, 0, 0, 3, 0, 0, -2, 0, 0, -1, 0, 0, 4, 0, 0,
     -3, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, -2, 0,
     0, -4, 0, 0, 2, 0, 0, -3, 0, 0, 0, 0, 0, 2, 0, 0, -3, 0, 0, -1,
     0, 0, 3, 0, 0, -2, 0, 0, 2, 0, 0, 6, 0, 0, -5, 0, 0, -3, 0, 0] := by
  eta_coeff

end WeightTwoCusps
