module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«225».New.«225_eta_1m1_3p1_5p4_25m1_75p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z)^(-1) η(3z) η(5z)^4 η(25z)^(-1) η(75z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(5z)^4 η(25z)^(-1) η(75z)` at level 450. -/
abbrev cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_old_450_1 : gamma0CuspForms 450 :=
  gamma0RescaleToLevel cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_old_450_1_eq_eta :
    cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_old_450_1 =
      etaQuotientCuspForm 450 sparse![450; 0 => -1, 2 => 1, 4 => 4, 24 => -1, 74 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_old_450_1_first_coeffs :
    first_coeffs 100 cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_old_450_1 =
    [0, 0, 0, 1, 1, 2, 2, 4, 1, 3, 1, 5, 0, 4, 1, 4, -4, 1, 0, 3,
     -2, 1, -1, 1, -8, -1, -3, 1, -7, 1, -4, 5, -3, -2, -1, 0, -2, -6, -3, 5,
     -3, -12, -2, 3, -6, -4, 1, 3, -2, -18, -2, -6, -8, -4, 2, 4, 0, 1, -2, 7,
     -4, 9, -1, 1, 10, -4, -12, 2, 0, -2, 0, 12, -2, -8, -14, 4, -5, -1, 2, 3,
     -2, 3, 3, 5, 2, -2, 5, 2, 2, 8, 4, -19, 2, -1, -5, 8, 16, 2, 3, -10] := by
  eta_coeff

end WeightTwoCusps
