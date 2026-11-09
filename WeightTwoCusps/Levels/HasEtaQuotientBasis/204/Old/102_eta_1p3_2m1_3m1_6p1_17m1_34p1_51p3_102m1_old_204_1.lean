module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«102».New.«102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 204

The eta expression is `η(z)^3 η(2z)^(-1) η(3z)^(-1) η(6z) η(17z)^(-1) η(34z) η(51z)^3 η(102z)^(-1)`; see
[the local level table](../../TABLE.md#level-204).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-1) η(3z)^(-1) η(6z) η(17z)^(-1) η(34z) η(51z)^3 η(102z)^(-1)` at level 204. -/
abbrev cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1_old_204_1 : gamma0CuspForms 204 :=
  gamma0RescaleToLevel cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1_old_204_1_eq_eta :
    cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1_old_204_1 =
      etaQuotientCuspForm 204 sparse![204; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 16 => -1, 33 => 1, 50 => 3, 101 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1_old_204_1_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1_old_204_1 =
    [0, 0, 0, 1, -3, 1, 3, -1, 0, -1, 0, -2, 0, -1, 3, 1, 3, 0, -3, 1,
     -2, -5, 1, 4, -1, 3, -4, 0, 1, 2, -4, 3, 4, 4, 0, -4, -2, -2, -8, 1,
     4, -3, 3, -3, 3, 1, 5, -4, 6, 2, 4, -1, -4, -2, -4, -3, -1, -3, -4, 4,
     2, 2, 5, 3, -5, -1, 3, -2, -1, 4, -4, 3, 1, 0, -2, -2, -2, 8, 2, -3,
     -4, 4, -4, -4, -7, -1, 6, 2, 1, 4, 4, 2, 1, -1, 2, -1, -5, -10, 6, -8] := by
  eta_coeff

end WeightTwoCusps
