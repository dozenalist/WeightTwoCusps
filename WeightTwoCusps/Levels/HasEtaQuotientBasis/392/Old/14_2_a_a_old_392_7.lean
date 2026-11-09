module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 392

The eta expression is `η(7z) η(14z) η(49z) η(98z)`; see
[the local level table](../../TABLE.md#level-392).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_14_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(7z) η(14z) η(49z) η(98z)` at level 392. -/
abbrev cuspForm_14_2_a_a_old_392_7 : gamma0CuspForms 392 :=
  gamma0RescaleToLevel cuspForm_14_2_a_a 7 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_14_2_a_a_old_392_7_eq_eta :
    cuspForm_14_2_a_a_old_392_7 =
      etaQuotientCuspForm 392 sparse![392; 6 => 1, 13 => 1, 48 => 1, 97 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_14_2_a_a_old_392_7_first_coeffs :
    first_coeffs 100 cuspForm_14_2_a_a_old_392_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
     0, -2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, -1, 0] := by
  eta_coeff

end WeightTwoCusps
