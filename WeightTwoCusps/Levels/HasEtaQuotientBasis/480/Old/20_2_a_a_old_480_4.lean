module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«20».New.«20_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(8z)^2 η(40z)^2`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_20_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z)^2 η(40z)^2` at level 480. -/
abbrev cuspForm_20_2_a_a_old_480_4 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_20_2_a_a 4 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_20_2_a_a_old_480_4_eq_eta :
    cuspForm_20_2_a_a_old_480_4 =
      etaQuotientCuspForm 480 sparse![480; 7 => 2, 39 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_20_2_a_a_old_480_4_first_coeffs :
    first_coeffs 100 cuspForm_20_2_a_a_old_480_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0,
     0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
