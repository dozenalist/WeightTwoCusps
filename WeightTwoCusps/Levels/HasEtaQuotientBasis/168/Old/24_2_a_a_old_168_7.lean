module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«24».New.«24_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 168

The eta expression is `η(14z) η(28z) η(42z) η(84z)`; see
[the local level table](../../TABLE.md#level-168).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_24_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(14z) η(28z) η(42z) η(84z)` at level 168. -/
abbrev cuspForm_24_2_a_a_old_168_7 : gamma0CuspForms 168 :=
  gamma0Rescale cuspForm_24_2_a_a 7

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_24_2_a_a_old_168_7_eq_eta :
    cuspForm_24_2_a_a_old_168_7 =
      etaQuotientCuspForm 168 sparse![168; 13 => 1, 27 => 1, 41 => 1, 83 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_24_2_a_a_old_168_7_first_coeffs :
    first_coeffs 100 cuspForm_24_2_a_a_old_168_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
