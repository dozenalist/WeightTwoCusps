module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«24».New.«24_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(2z) η(4z) η(6z) η(12z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_24_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z) η(6z) η(12z)` at level 480. -/
abbrev cuspForm_24_2_a_a_old_480_1 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_24_2_a_a 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_24_2_a_a_old_480_1_eq_eta :
    cuspForm_24_2_a_a_old_480_1 =
      etaQuotientCuspForm 480 sparse![480; 1 => 1, 3 => 1, 5 => 1, 11 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_24_2_a_a_old_480_1_first_coeffs :
    first_coeffs 100 cuspForm_24_2_a_a_old_480_1 =
    [0, 1, 0, -1, 0, -2, 0, 0, 0, 1, 0, 4, 0, -2, 0, 2, 0, 2, 0, -4,
     0, 0, 0, -8, 0, -1, 0, -1, 0, 6, 0, 8, 0, -4, 0, 0, 0, 6, 0, 2,
     0, -6, 0, 4, 0, -2, 0, 0, 0, -7, 0, -2, 0, -2, 0, -8, 0, 4, 0, 4,
     0, -2, 0, 0, 0, 4, 0, -4, 0, 8, 0, 8, 0, 10, 0, 1, 0, 0, 0, -8,
     0, 1, 0, -4, 0, -4, 0, -6, 0, -6, 0, 0, 0, -8, 0, 8, 0, 2, 0, 4] := by
  eta_coeff

end WeightTwoCusps
