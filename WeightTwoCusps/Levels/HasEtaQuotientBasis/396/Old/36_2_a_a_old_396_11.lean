module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«36».New.«36_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(66z)^4`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(11z)` of `cuspForm_36_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(66z)^4` at level 396. -/
abbrev cuspForm_36_2_a_a_old_396_11 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_36_2_a_a 11

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_36_2_a_a_old_396_11_eq_eta :
    cuspForm_36_2_a_a_old_396_11 =
      etaQuotientCuspForm 396 sparse![396; 65 => 4] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_36_2_a_a_old_396_11_first_coeffs :
    first_coeffs 100 cuspForm_36_2_a_a_old_396_11 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
