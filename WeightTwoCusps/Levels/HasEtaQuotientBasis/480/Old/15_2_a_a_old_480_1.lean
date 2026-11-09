module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(z) η(3z) η(5z) η(15z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(3z) η(5z) η(15z)` at level 480. -/
abbrev cuspForm_15_2_a_a_old_480_1 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_15_2_a_a 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_480_1_eq_eta :
    cuspForm_15_2_a_a_old_480_1 =
      etaQuotientCuspForm 480 sparse![480; 0 => 1, 2 => 1, 4 => 1, 14 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_480_1_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_480_1 =
    [0, 1, -1, -1, -1, 1, 1, 0, 3, 1, -1, -4, 1, -2, 0, -1, -1, 2, -1, 4,
     -1, 0, 4, 0, -3, 1, 2, -1, 0, -2, 1, 0, -5, 4, -2, 0, -1, -10, -4, 2,
     3, 10, 0, 4, 4, 1, 0, 8, 1, -7, -1, -2, 2, -10, 1, -4, 0, -4, 2, -4,
     1, -2, 0, 0, 7, -2, -4, 12, -2, 0, 0, -8, 3, 10, 10, -1, -4, 0, -2, 0,
     -1, 1, -10, 12, 0, 2, -4, 2, -12, -6, -1, 0, 0, 0, -8, 4, 5, 2, 7, -4] := by
  eta_coeff

end WeightTwoCusps
