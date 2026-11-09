module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«27».New.«27_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 54

The eta expression is `η(6z)^2 η(18z)^2`; see
[the local level table](../../TABLE.md#level-54).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_27_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^2 η(18z)^2` at level 54. -/
abbrev cuspForm_27_2_a_a_old_54_2 : gamma0CuspForms 54 :=
  gamma0Rescale cuspForm_27_2_a_a 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_27_2_a_a_old_54_2_eq_eta :
    cuspForm_27_2_a_a_old_54_2 =
      etaQuotientCuspForm 54 sparse![54; 5 => 2, 17 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_27_2_a_a_old_54_2_first_coeffs :
    first_coeffs 100 cuspForm_27_2_a_a_old_54_2 =
    [0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, -7, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 2, 0, 0, 0,
     0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0] := by
  eta_coeff

end WeightTwoCusps
