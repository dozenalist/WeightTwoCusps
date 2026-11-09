module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«24».New.«24_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 72

The eta expression is `η(6z) η(12z) η(18z) η(36z)`; see
[the local level table](../../TABLE.md#level-72).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_24_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(12z) η(18z) η(36z)` at level 72. -/
abbrev cuspForm_24_2_a_a_old_72_3 : gamma0CuspForms 72 :=
  gamma0Rescale cuspForm_24_2_a_a 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_24_2_a_a_old_72_3_eq_eta :
    cuspForm_24_2_a_a_old_72_3 =
      etaQuotientCuspForm 72 sparse![72; 5 => 1, 11 => 1, 17 => 1, 35 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_24_2_a_a_old_72_3_first_coeffs :
    first_coeffs 100 cuspForm_24_2_a_a_old_72_3 =
    [0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, -2,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
