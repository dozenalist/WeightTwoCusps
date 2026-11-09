module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«11».New.«11_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(z)^2 η(11z)^2`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_11_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(11z)^2` at level 352. -/
abbrev cuspForm_11_2_a_a_old_352_1 : gamma0CuspForms 352 :=
  gamma0RescaleToLevel cuspForm_11_2_a_a 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_11_2_a_a_old_352_1_eq_eta :
    cuspForm_11_2_a_a_old_352_1 =
      etaQuotientCuspForm 352 sparse![352; 0 => 2, 10 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_11_2_a_a_old_352_1_first_coeffs :
    first_coeffs 100 cuspForm_11_2_a_a_old_352_1 =
    [0, 1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, -2, 4, 4, -1, -4, -2, 4, 0,
     2, 2, -2, -1, 0, -4, -8, 5, -4, 0, 2, 7, 8, -1, 4, -2, -4, 3, 0, -4,
     0, -8, -4, -6, 2, -2, 2, 8, 4, -3, 8, 2, 8, -6, -10, 1, 0, 0, 0, 5,
     -2, 12, -14, 4, -8, 4, 2, -7, -4, 1, 4, -3, 0, 4, -6, 4, 0, -2, 8, -10,
     -4, 1, 16, -6, 4, -2, 12, 0, 0, 15, 4, -8, -2, -7, -16, 0, -8, -7, 6, -2] := by
  eta_coeff

end WeightTwoCusps
