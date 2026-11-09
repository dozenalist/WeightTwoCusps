module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«24».New.«24_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(10z) η(20z) η(30z) η(60z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_24_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(10z) η(20z) η(30z) η(60z)` at level 480. -/
abbrev cuspForm_24_2_a_a_old_480_5 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_24_2_a_a 5 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_24_2_a_a_old_480_5_eq_eta :
    cuspForm_24_2_a_a_old_480_5 =
      etaQuotientCuspForm 480 sparse![480; 9 => 1, 19 => 1, 29 => 1, 59 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_24_2_a_a_old_480_5_first_coeffs :
    first_coeffs 100 cuspForm_24_2_a_a_old_480_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
