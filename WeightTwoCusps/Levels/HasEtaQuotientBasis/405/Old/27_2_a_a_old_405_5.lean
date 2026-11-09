module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«27».New.«27_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 405

The eta expression is `η(15z)^2 η(45z)^2`; see
[the local level table](../../TABLE.md#level-405).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_27_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(15z)^2 η(45z)^2` at level 405. -/
abbrev cuspForm_27_2_a_a_old_405_5 : gamma0CuspForms 405 :=
  gamma0RescaleToLevel cuspForm_27_2_a_a 5 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_27_2_a_a_old_405_5_eq_eta :
    cuspForm_27_2_a_a_old_405_5 =
      etaQuotientCuspForm 405 sparse![405; 14 => 2, 44 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_27_2_a_a_old_405_5_first_coeffs :
    first_coeffs 100 cuspForm_27_2_a_a_old_405_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
