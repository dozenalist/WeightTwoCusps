module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 224

The eta expression is `η(4z) η(8z) η(28z) η(56z)`; see
[the local level table](../../TABLE.md#level-224).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_14_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(8z) η(28z) η(56z)` at level 224. -/
abbrev cuspForm_14_2_a_a_old_224_4 : gamma0CuspForms 224 :=
  gamma0RescaleToLevel cuspForm_14_2_a_a 4 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_14_2_a_a_old_224_4_eq_eta :
    cuspForm_14_2_a_a_old_224_4 =
      etaQuotientCuspForm 224 sparse![224; 3 => 1, 7 => 1, 27 => 1, 55 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_14_2_a_a_old_224_4_first_coeffs :
    first_coeffs 100 cuspForm_14_2_a_a_old_224_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -4, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 6, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
