module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«20».New.«20_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(2z)^2 η(10z)^2`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_20_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(10z)^2` at level 480. -/
abbrev cuspForm_20_2_a_a_old_480_1 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_20_2_a_a 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_20_2_a_a_old_480_1_eq_eta :
    cuspForm_20_2_a_a_old_480_1 =
      etaQuotientCuspForm 480 sparse![480; 1 => 2, 9 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_20_2_a_a_old_480_1_first_coeffs :
    first_coeffs 100 cuspForm_20_2_a_a_old_480_1 =
    [0, 1, 0, -2, 0, -1, 0, 2, 0, 1, 0, 0, 0, 2, 0, 2, 0, -6, 0, -4,
     0, -4, 0, 6, 0, 1, 0, 4, 0, 6, 0, -4, 0, 0, 0, -2, 0, 2, 0, -4,
     0, 6, 0, -10, 0, -1, 0, -6, 0, -3, 0, 12, 0, -6, 0, 0, 0, 8, 0, 12,
     0, 2, 0, 2, 0, -2, 0, 2, 0, -12, 0, -12, 0, 2, 0, -2, 0, 0, 0, 8,
     0, -11, 0, 6, 0, 6, 0, -12, 0, -6, 0, 4, 0, 8, 0, 4, 0, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
