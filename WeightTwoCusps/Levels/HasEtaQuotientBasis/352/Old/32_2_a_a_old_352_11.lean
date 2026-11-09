module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«32».New.«32_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(44z)^2 η(88z)^2`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(11z)` of `cuspForm_32_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(44z)^2 η(88z)^2` at level 352. -/
abbrev cuspForm_32_2_a_a_old_352_11 : gamma0CuspForms 352 :=
  gamma0Rescale cuspForm_32_2_a_a 11

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_32_2_a_a_old_352_11_eq_eta :
    cuspForm_32_2_a_a_old_352_11 =
      etaQuotientCuspForm 352 sparse![352; 43 => 2, 87 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_32_2_a_a_old_352_11_first_coeffs :
    first_coeffs 100 cuspForm_32_2_a_a_old_352_11 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3] := by
  eta_coeff

end WeightTwoCusps
