module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(11z) η(22z) η(77z) η(154z)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(11z)` of `cuspForm_14_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(11z) η(22z) η(77z) η(154z)` at level 308. -/
abbrev cuspForm_14_2_a_a_old_308_11 : gamma0CuspForms 308 :=
  gamma0RescaleToLevel cuspForm_14_2_a_a 11 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_14_2_a_a_old_308_11_eq_eta :
    cuspForm_14_2_a_a_old_308_11 =
      etaQuotientCuspForm 308 sparse![308; 10 => 1, 21 => 1, 76 => 1, 153 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_14_2_a_a_old_308_11_first_coeffs :
    first_coeffs 100 cuspForm_14_2_a_a_old_308_11 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
