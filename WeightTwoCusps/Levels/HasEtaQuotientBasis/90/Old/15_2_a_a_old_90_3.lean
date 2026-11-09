module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 90

The eta expression is `η(3z) η(9z) η(15z) η(45z)`; see
[the local level table](../../TABLE.md#level-90).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(9z) η(15z) η(45z)` at level 90. -/
abbrev cuspForm_15_2_a_a_old_90_3 : gamma0CuspForms 90 :=
  gamma0RescaleToLevel cuspForm_15_2_a_a 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_90_3_eq_eta :
    cuspForm_15_2_a_a_old_90_3 =
      etaQuotientCuspForm 90 sparse![90; 2 => 1, 8 => 1, 14 => 1, 44 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_90_3_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_90_3 =
    [0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0,
     0, 0, 0, 0, 3, 0, 0, 1, 0, 0, -1, 0, 0, -4, 0, 0, 1, 0, 0, -2,
     0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 2, 0, 0, -1, 0, 0, 4, 0, 0,
     -1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, -3, 0, 0, 1, 0, 0, 2, 0,
     0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -5, 0, 0, 4] := by
  eta_coeff

end WeightTwoCusps
