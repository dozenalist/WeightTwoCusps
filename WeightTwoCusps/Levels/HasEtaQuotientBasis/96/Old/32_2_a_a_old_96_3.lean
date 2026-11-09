module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«32».New.«32_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 96

The eta expression is `η(12z)^2 η(24z)^2`; see
[the local level table](../../TABLE.md#level-96).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_32_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(12z)^2 η(24z)^2` at level 96. -/
abbrev cuspForm_32_2_a_a_old_96_3 : gamma0CuspForms 96 :=
  gamma0Rescale cuspForm_32_2_a_a 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_32_2_a_a_old_96_3_eq_eta :
    cuspForm_32_2_a_a_old_96_3 =
      etaQuotientCuspForm 96 sparse![96; 11 => 2, 23 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_32_2_a_a_old_96_3_first_coeffs :
    first_coeffs 100 cuspForm_32_2_a_a_old_96_3 =
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
