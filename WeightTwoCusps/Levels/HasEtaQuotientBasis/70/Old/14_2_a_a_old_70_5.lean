module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 70

The eta expression is `η(5z) η(10z) η(35z) η(70z)`; see
[the local level table](../../TABLE.md#level-70).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_14_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z) η(10z) η(35z) η(70z)` at level 70. -/
abbrev cuspForm_14_2_a_a_old_70_5 : gamma0CuspForms 70 :=
  gamma0Rescale cuspForm_14_2_a_a 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_14_2_a_a_old_70_5_eq_eta :
    cuspForm_14_2_a_a_old_70_5 =
      etaQuotientCuspForm 70 sparse![70; 4 => 1, 9 => 1, 34 => 1, 69 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_14_2_a_a_old_70_5_first_coeffs :
    first_coeffs 100 cuspForm_14_2_a_a_old_70_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 6, 0, 0, 0, 0, -1, 0, 0, 0, 0, 2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
