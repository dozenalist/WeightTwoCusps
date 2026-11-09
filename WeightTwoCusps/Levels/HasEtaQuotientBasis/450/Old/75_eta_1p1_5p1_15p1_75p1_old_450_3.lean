module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«75».New.«75_eta_1p1_5p1_15p1_75p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(3z) η(15z) η(45z) η(225z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_75_eta_1p1_5p1_15p1_75p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(15z) η(45z) η(225z)` at level 450. -/
abbrev cuspForm_75_eta_1p1_5p1_15p1_75p1_old_450_3 : gamma0CuspForms 450 :=
  gamma0RescaleToLevel cuspForm_75_eta_1p1_5p1_15p1_75p1 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_75_eta_1p1_5p1_15p1_75p1_old_450_3_eq_eta :
    cuspForm_75_eta_1p1_5p1_15p1_75p1_old_450_3 =
      etaQuotientCuspForm 450 sparse![450; 2 => 1, 14 => 1, 44 => 1, 224 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_75_eta_1p1_5p1_15p1_75p1_old_450_3_first_coeffs :
    first_coeffs 100 cuspForm_75_eta_1p1_5p1_15p1_75p1_old_450_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0,
     0, 0, -2, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0,
     1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 4, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
