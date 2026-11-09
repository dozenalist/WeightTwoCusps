module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«20».New.«20_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 140

The eta expression is `η(14z)^2 η(70z)^2`; see
[the local level table](../../TABLE.md#level-140).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_20_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(14z)^2 η(70z)^2` at level 140. -/
abbrev cuspForm_20_2_a_a_old_140_7 : gamma0CuspForms 140 :=
  gamma0Rescale cuspForm_20_2_a_a 7

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_20_2_a_a_old_140_7_eq_eta :
    cuspForm_20_2_a_a_old_140_7 =
      etaQuotientCuspForm 140 sparse![140; 13 => 2, 69 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_20_2_a_a_old_140_7_first_coeffs :
    first_coeffs 100 cuspForm_20_2_a_a_old_140_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
