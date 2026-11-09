module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(24z) η(48z) η(168z) η(336z)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(24z)` of `cuspForm_14_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(24z) η(48z) η(168z) η(336z)` at level 336. -/
abbrev cuspForm_14_2_a_a_old_336_24 : gamma0CuspForms 336 :=
  gamma0Rescale cuspForm_14_2_a_a 24

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_14_2_a_a_old_336_24_eq_eta :
    cuspForm_14_2_a_a_old_336_24 =
      etaQuotientCuspForm 336 sparse![336; 23 => 1, 47 => 1, 167 => 1, 335 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_14_2_a_a_old_336_24_first_coeffs :
    first_coeffs 100 cuspForm_14_2_a_a_old_336_24 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
