module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«102».New.«102_eta_1p2_3m1_6p1_17p1_34m1_102p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(2z)^2 η(6z)^(-1) η(12z) η(34z) η(68z)^(-1) η(204z)^2`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_102_eta_1p2_3m1_6p1_17p1_34m1_102p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(6z)^(-1) η(12z) η(34z) η(68z)^(-1) η(204z)^2` at level 408. -/
abbrev cuspForm_102_eta_1p2_3m1_6p1_17p1_34m1_102p2_old_408_2 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_102_eta_1p2_3m1_6p1_17p1_34m1_102p2 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_102_eta_1p2_3m1_6p1_17p1_34m1_102p2_old_408_2_eq_eta :
    cuspForm_102_eta_1p2_3m1_6p1_17p1_34m1_102p2_old_408_2 =
      etaQuotientCuspForm 408 sparse![408; 1 => 2, 5 => -1, 11 => 1, 33 => 1, 67 => -1, 203 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1p2_3m1_6p1_17p1_34m1_102p2_old_408_2_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1p2_3m1_6p1_17p1_34m1_102p2_old_408_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -2, 0,
     -1, 0, 3, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, -2, 0, -2, 0,
     2, 0, 1, 0, 3, 0, -1, 0, 1, 0, -1, 0, 2, 0, 0, 0, -4, 0, 2, 0,
     -1, 0, -2, 0, -2, 0, 3, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0,
     3, 0, -2, 0, 2, 0, 1, 0, 1, 0, 1, 0, -4, 0, -1, 0, 2, 0, 3, 0] := by
  eta_coeff

end WeightTwoCusps
