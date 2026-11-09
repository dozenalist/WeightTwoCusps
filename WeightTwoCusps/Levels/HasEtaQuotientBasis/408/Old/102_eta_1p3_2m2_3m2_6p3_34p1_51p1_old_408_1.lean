module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«102».New.«102_eta_1p3_2m2_3m2_6p3_34p1_51p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(z)^3 η(2z)^(-2) η(3z)^(-2) η(6z)^3 η(34z) η(51z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_102_eta_1p3_2m2_3m2_6p3_34p1_51p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-2) η(3z)^(-2) η(6z)^3 η(34z) η(51z)` at level 408. -/
abbrev cuspForm_102_eta_1p3_2m2_3m2_6p3_34p1_51p1_old_408_1 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_102_eta_1p3_2m2_3m2_6p3_34p1_51p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_102_eta_1p3_2m2_3m2_6p3_34p1_51p1_old_408_1_eq_eta :
    cuspForm_102_eta_1p3_2m2_3m2_6p3_34p1_51p1_old_408_1 =
      etaQuotientCuspForm 408 sparse![408; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 33 => 1, 50 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1p3_2m2_3m2_6p3_34p1_51p1_old_408_1_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1p3_2m2_3m2_6p3_34p1_51p1_old_408_1 =
    [0, 0, 0, 0, 1, -3, 2, 1, -1, -1, 3, -1, 0, -2, -2, 2, 0, 0, 1, 3,
     0, -2, -2, 1, -1, 0, 2, 1, -1, 0, -3, -1, -2, 3, 0, 3, 0, 1, 1, 3,
     -5, -1, 1, 0, -2, -2, -1, 5, 1, -1, 0, 0, -2, -1, -3, 1, 6, -2, -1, 0,
     2, -7, 2, 1, 7, 7, 1, -5, 0, -5, -3, -2, -4, 4, 0, -3, 1, 0, -4, 7,
     4, 3, 4, -2, -4, 0, -2, -6, 0, 1, 0, 2, 4, 0, -5, 1, 6, 2, -3, -4] := by
  eta_coeff

end WeightTwoCusps
