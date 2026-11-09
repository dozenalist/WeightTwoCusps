module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«24».New.«24_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 48

The eta expression is `η(4z) η(8z) η(12z) η(24z)`; see
[the local level table](../../TABLE.md#level-48).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_24_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(8z) η(12z) η(24z)` at level 48. -/
abbrev cuspForm_24_2_a_a_old_48_2 : gamma0CuspForms 48 :=
  gamma0Rescale cuspForm_24_2_a_a 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_24_2_a_a_old_48_2_eq_eta :
    cuspForm_24_2_a_a_old_48_2 =
      etaQuotientCuspForm 48 sparse![48; 3 => 1, 7 => 1, 11 => 1, 23 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_24_2_a_a_old_48_2_first_coeffs :
    first_coeffs 100 cuspForm_24_2_a_a_old_48_2 =
    [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 4, 0, 0, 0, -2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, -4, 0,
     0, 0, 0, 0, 0, 0, -8, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 6, 0,
     0, 0, 8, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0,
     0, 0, -6, 0, 0, 0, 4, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -7, 0] := by
  eta_coeff

end WeightTwoCusps
