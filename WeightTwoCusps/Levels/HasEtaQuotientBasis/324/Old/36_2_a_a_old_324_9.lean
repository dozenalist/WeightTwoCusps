module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«36».New.«36_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(54z)^4`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(9z)` of `cuspForm_36_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(54z)^4` at level 324. -/
abbrev cuspForm_36_2_a_a_old_324_9 : gamma0CuspForms 324 :=
  gamma0Rescale cuspForm_36_2_a_a 9

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_36_2_a_a_old_324_9_eq_eta :
    cuspForm_36_2_a_a_old_324_9 =
      etaQuotientCuspForm 324 sparse![324; 53 => 4] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_36_2_a_a_old_324_9_first_coeffs :
    first_coeffs 100 cuspForm_36_2_a_a_old_324_9 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
