module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 90

The eta expression is `η(2z) η(6z) η(10z) η(30z)`; see
[the local level table](../../TABLE.md#level-90).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(6z) η(10z) η(30z)` at level 90. -/
abbrev cuspForm_15_2_a_a_old_90_2 : gamma0CuspForms 90 :=
  gamma0RescaleToLevel cuspForm_15_2_a_a 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_90_2_eq_eta :
    cuspForm_15_2_a_a_old_90_2 =
      etaQuotientCuspForm 90 sparse![90; 1 => 1, 5 => 1, 9 => 1, 29 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_90_2_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_90_2 =
    [0, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 1, 0,
     -1, 0, -4, 0, 1, 0, -2, 0, 0, 0, -1, 0, -1, 0, 2, 0, -1, 0, 4, 0,
     -1, 0, 0, 0, 4, 0, 0, 0, -3, 0, 1, 0, 2, 0, -1, 0, 0, 0, -2, 0,
     1, 0, 0, 0, -5, 0, 4, 0, -2, 0, 0, 0, -1, 0, -10, 0, -4, 0, 2, 0,
     3, 0, 10, 0, 0, 0, 4, 0, 4, 0, 1, 0, 0, 0, 8, 0, 1, 0, -7, 0] := by
  eta_coeff

end WeightTwoCusps
