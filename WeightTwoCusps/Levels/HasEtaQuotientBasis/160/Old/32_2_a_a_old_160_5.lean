module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«32».New.«32_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 160

The eta expression is `η(20z)^2 η(40z)^2`; see
[the local level table](../../TABLE.md#level-160).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_32_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(20z)^2 η(40z)^2` at level 160. -/
abbrev cuspForm_32_2_a_a_old_160_5 : gamma0CuspForms 160 :=
  gamma0Rescale cuspForm_32_2_a_a 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_32_2_a_a_old_160_5_eq_eta :
    cuspForm_32_2_a_a_old_160_5 =
      etaQuotientCuspForm 160 sparse![160; 19 => 2, 39 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_32_2_a_a_old_160_5_first_coeffs :
    first_coeffs 100 cuspForm_32_2_a_a_old_160_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
