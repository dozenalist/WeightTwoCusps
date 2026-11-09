module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«27».New.«27_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(54z)^2 η(162z)^2`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(18z)` of `cuspForm_27_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(54z)^2 η(162z)^2` at level 486. -/
abbrev cuspForm_27_2_a_a_old_486_18 : gamma0CuspForms 486 :=
  gamma0Rescale cuspForm_27_2_a_a 18

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_27_2_a_a_old_486_18_eq_eta :
    cuspForm_27_2_a_a_old_486_18 =
      etaQuotientCuspForm 486 sparse![486; 53 => 2, 161 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_27_2_a_a_old_486_18_first_coeffs :
    first_coeffs 100 cuspForm_27_2_a_a_old_486_18 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
