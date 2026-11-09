module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 150

The eta expression is `η(5z) η(15z) η(25z) η(75z)`; see
[the local level table](../../TABLE.md#level-150).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z) η(15z) η(25z) η(75z)` at level 150. -/
abbrev cuspForm_15_2_a_a_old_150_5 : gamma0CuspForms 150 :=
  gamma0RescaleToLevel cuspForm_15_2_a_a 5 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_150_5_eq_eta :
    cuspForm_15_2_a_a_old_150_5 =
      etaQuotientCuspForm 150 sparse![150; 4 => 1, 14 => 1, 24 => 1, 74 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_150_5_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_150_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     3, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -4, 0, 0, 0, 0,
     1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 4, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
