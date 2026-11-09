module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(14z) η(42z) η(70z) η(210z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(14z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(14z) η(42z) η(70z) η(210z)` at level 420. -/
abbrev cuspForm_15_2_a_a_old_420_14 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_15_2_a_a 14 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_420_14_eq_eta :
    cuspForm_15_2_a_a_old_420_14 =
      etaQuotientCuspForm 420 sparse![420; 13 => 1, 41 => 1, 69 => 1, 209 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_420_14_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_420_14 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
