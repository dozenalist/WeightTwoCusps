module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«11».New.«11_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(2z)^2 η(22z)^2`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_11_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(22z)^2` at level 396. -/
abbrev cuspForm_11_2_a_a_old_396_2 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_11_2_a_a 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_11_2_a_a_old_396_2_eq_eta :
    cuspForm_11_2_a_a_old_396_2 =
      etaQuotientCuspForm 396 sparse![396; 1 => 2, 21 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_11_2_a_a_old_396_2_first_coeffs :
    first_coeffs 100 cuspForm_11_2_a_a_old_396_2 =
    [0, 0, 1, 0, -2, 0, -1, 0, 2, 0, 1, 0, 2, 0, -2, 0, 0, 0, -2, 0,
     -2, 0, 1, 0, -2, 0, 4, 0, 4, 0, -1, 0, -4, 0, -2, 0, 4, 0, 0, 0,
     2, 0, 2, 0, -2, 0, -1, 0, 0, 0, -4, 0, -8, 0, 5, 0, -4, 0, 0, 0,
     2, 0, 7, 0, 8, 0, -1, 0, 4, 0, -2, 0, -4, 0, 3, 0, 0, 0, -4, 0,
     0, 0, -8, 0, -4, 0, -6, 0, 2, 0, -2, 0, 2, 0, 8, 0, 4, 0, -3, 0] := by
  eta_coeff

end WeightTwoCusps
