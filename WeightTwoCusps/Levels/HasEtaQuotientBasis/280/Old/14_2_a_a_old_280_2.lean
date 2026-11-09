module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(2z) η(4z) η(14z) η(28z)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_14_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z) η(14z) η(28z)` at level 280. -/
abbrev cuspForm_14_2_a_a_old_280_2 : gamma0CuspForms 280 :=
  gamma0RescaleToLevel cuspForm_14_2_a_a 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_14_2_a_a_old_280_2_eq_eta :
    cuspForm_14_2_a_a_old_280_2 =
      etaQuotientCuspForm 280 sparse![280; 1 => 1, 3 => 1, 13 => 1, 27 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_14_2_a_a_old_280_2_first_coeffs :
    first_coeffs 100 cuspForm_14_2_a_a_old_280_2 =
    [0, 0, 1, 0, -1, 0, -2, 0, 1, 0, 0, 0, 2, 0, 1, 0, -1, 0, 1, 0,
     0, 0, 0, 0, -2, 0, -4, 0, -1, 0, 0, 0, 1, 0, 6, 0, -1, 0, 2, 0,
     0, 0, -2, 0, 0, 0, 0, 0, 2, 0, -5, 0, 4, 0, 4, 0, 1, 0, -6, 0,
     0, 0, -4, 0, -1, 0, 0, 0, -6, 0, 0, 0, 1, 0, 2, 0, -2, 0, 8, 0,
     0, 0, 6, 0, 2, 0, 8, 0, 0, 0, 0, 0, 0, 0, -12, 0, -2, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
