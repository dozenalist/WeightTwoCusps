module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(26z) η(78z) η(130z) η(390z)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(26z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(26z) η(78z) η(130z) η(390z)` at level 390. -/
abbrev cuspForm_15_2_a_a_old_390_26 : gamma0CuspForms 390 :=
  gamma0Rescale cuspForm_15_2_a_a 26

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_390_26_eq_eta :
    cuspForm_15_2_a_a_old_390_26 =
      etaQuotientCuspForm 390 sparse![390; 25 => 1, 77 => 1, 129 => 1, 389 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_390_26_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_390_26 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
