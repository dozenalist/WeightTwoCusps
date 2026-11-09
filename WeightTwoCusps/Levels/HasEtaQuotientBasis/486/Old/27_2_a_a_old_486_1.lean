module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«27».New.«27_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(3z)^2 η(9z)^2`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_27_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^2 η(9z)^2` at level 486. -/
abbrev cuspForm_27_2_a_a_old_486_1 : gamma0CuspForms 486 :=
  gamma0RescaleToLevel cuspForm_27_2_a_a 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_27_2_a_a_old_486_1_eq_eta :
    cuspForm_27_2_a_a_old_486_1 =
      etaQuotientCuspForm 486 sparse![486; 2 => 2, 8 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_27_2_a_a_old_486_1_first_coeffs :
    first_coeffs 100 cuspForm_27_2_a_a_old_486_1 =
    [0, 1, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 5, 0, 0, 4, 0, 0, -7,
     0, 0, 0, 0, 0, -5, 0, 0, 2, 0, 0, -4, 0, 0, 0, 0, 0, 11, 0, 0,
     0, 0, 0, 8, 0, 0, 0, 0, 0, -6, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0,
     0, -1, 0, 0, -8, 0, 0, 5, 0, 0, 0, 0, 0, -7, 0, 0, 14, 0, 0, 17,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, -19, 0, 0] := by
  eta_coeff

end WeightTwoCusps
