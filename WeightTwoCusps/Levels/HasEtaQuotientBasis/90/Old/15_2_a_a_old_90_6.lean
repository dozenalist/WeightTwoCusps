module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 90

The eta expression is `η(6z) η(18z) η(30z) η(90z)`; see
[the local level table](../../TABLE.md#level-90).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(18z) η(30z) η(90z)` at level 90. -/
abbrev cuspForm_15_2_a_a_old_90_6 : gamma0CuspForms 90 :=
  gamma0Rescale cuspForm_15_2_a_a 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_90_6_eq_eta :
    cuspForm_15_2_a_a_old_90_6 =
      etaQuotientCuspForm 90 sparse![90; 5 => 1, 17 => 1, 29 => 1, 89 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_90_6_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_90_6 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
