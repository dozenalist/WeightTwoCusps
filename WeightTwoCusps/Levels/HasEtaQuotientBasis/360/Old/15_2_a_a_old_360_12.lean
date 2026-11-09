module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(12z) η(36z) η(60z) η(180z)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(12z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(12z) η(36z) η(60z) η(180z)` at level 360. -/
abbrev cuspForm_15_2_a_a_old_360_12 : gamma0CuspForms 360 :=
  gamma0RescaleToLevel cuspForm_15_2_a_a 12 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_360_12_eq_eta :
    cuspForm_15_2_a_a_old_360_12 =
      etaQuotientCuspForm 360 sparse![360; 11 => 1, 35 => 1, 59 => 1, 179 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_360_12_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_360_12 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
