module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(16z) η(48z) η(80z) η(240z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(16z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(16z) η(48z) η(80z) η(240z)` at level 480. -/
abbrev cuspForm_15_2_a_a_old_480_16 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_15_2_a_a 16 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_480_16_eq_eta :
    cuspForm_15_2_a_a_old_480_16 =
      etaQuotientCuspForm 480 sparse![480; 15 => 1, 47 => 1, 79 => 1, 239 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_480_16_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_480_16 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
