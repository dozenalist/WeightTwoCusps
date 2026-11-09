module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«36».New.«36_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(6z)^4`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_36_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^4` at level 396. -/
abbrev cuspForm_36_2_a_a_old_396_1 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_36_2_a_a 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_36_2_a_a_old_396_1_eq_eta :
    cuspForm_36_2_a_a_old_396_1 =
      etaQuotientCuspForm 396 sparse![396; 5 => 4] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_36_2_a_a_old_396_1_first_coeffs :
    first_coeffs 100 cuspForm_36_2_a_a_old_396_1 =
    [0, 1, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 8,
     0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, -10, 0, 0,
     0, 0, 0, 8, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 14, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, -4,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 14, 0, 0] := by
  eta_coeff

end WeightTwoCusps
