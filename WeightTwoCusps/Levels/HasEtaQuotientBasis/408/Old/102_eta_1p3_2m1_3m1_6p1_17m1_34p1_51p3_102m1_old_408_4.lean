module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«102».New.«102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(4z)^3 η(8z)^(-1) η(12z)^(-1) η(24z) η(68z)^(-1) η(136z) η(204z)^3 η(408z)^(-1)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^3 η(8z)^(-1) η(12z)^(-1) η(24z) η(68z)^(-1) η(136z) η(204z)^3 η(408z)^(-1)` at level 408. -/
abbrev cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1_old_408_4 : gamma0CuspForms 408 :=
  gamma0Rescale cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1_old_408_4_eq_eta :
    cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1_old_408_4 =
      etaQuotientCuspForm 408 sparse![408; 3 => 3, 7 => -1, 11 => -1, 23 => 1, 67 => -1, 135 => 1, 203 => 3, 407 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1_old_408_4_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1p3_2m1_3m1_6p1_17m1_34p1_51p3_102m1_old_408_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -3, 0, 0, 0,
     1, 0, 0, 0, 3, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 3, 0, 0, 0,
     1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 1, 0, 0, 0,
     -2, 0, 0, 0, -5, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
