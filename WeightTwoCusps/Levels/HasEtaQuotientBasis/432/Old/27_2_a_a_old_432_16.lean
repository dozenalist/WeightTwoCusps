module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«27».New.«27_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(48z)^2 η(144z)^2`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(16z)` of `cuspForm_27_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(48z)^2 η(144z)^2` at level 432. -/
abbrev cuspForm_27_2_a_a_old_432_16 : gamma0CuspForms 432 :=
  gamma0Rescale cuspForm_27_2_a_a 16

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_27_2_a_a_old_432_16_eq_eta :
    cuspForm_27_2_a_a_old_432_16 =
      etaQuotientCuspForm 432 sparse![432; 47 => 2, 143 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_27_2_a_a_old_432_16_first_coeffs :
    first_coeffs 100 cuspForm_27_2_a_a_old_432_16 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
