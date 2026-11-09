module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 60

The eta expression is `η(4z) η(12z) η(20z) η(60z)`; see
[the local level table](../../TABLE.md#level-60).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(12z) η(20z) η(60z)` at level 60. -/
abbrev cuspForm_15_2_a_a_old_60_4 : gamma0CuspForms 60 :=
  gamma0Rescale cuspForm_15_2_a_a 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_60_4_eq_eta :
    cuspForm_15_2_a_a_old_60_4 =
      etaQuotientCuspForm 60 sparse![60; 3 => 1, 11 => 1, 19 => 1, 59 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_60_4_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_60_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0,
     -1, 0, 0, 0, -4, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0, 4, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
