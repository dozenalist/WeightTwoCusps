module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z) η(2z) η(7z) η(14z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_14_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z) η(7z) η(14z)` at level 420. -/
abbrev cuspForm_14_2_a_a_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_14_2_a_a 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_14_2_a_a_old_420_1_eq_eta :
    cuspForm_14_2_a_a_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => 1, 1 => 1, 6 => 1, 13 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_14_2_a_a_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_14_2_a_a_old_420_1 =
    [0, 1, -1, -2, 1, 0, 2, 1, -1, 1, 0, 0, -2, -4, -1, 0, 1, 6, -1, 2,
     0, -2, 0, 0, 2, -5, 4, 4, 1, -6, 0, -4, -1, 0, -6, 0, 1, 2, -2, 8,
     0, 6, 2, 8, 0, 0, 0, -12, -2, 1, 5, -12, -4, 6, -4, 0, -1, -4, 6, -6,
     0, 8, 4, 1, 1, 0, 0, -4, 6, 0, 0, 0, -1, 2, -2, 10, 2, 0, -8, 8,
     0, -11, -6, -6, -2, 0, -8, 12, 0, -6, 0, -4, 0, 8, 12, 0, 2, -10, -1, 0] := by
  eta_coeff

end WeightTwoCusps
