module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«102».New.«102_eta_2p2_3p1_6m1_17m1_34p1_51p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(2z)^2 η(3z) η(6z)^(-1) η(17z)^(-1) η(34z) η(51z)^2`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_102_eta_2p2_3p1_6m1_17m1_34p1_51p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(3z) η(6z)^(-1) η(17z)^(-1) η(34z) η(51z)^2` at level 408. -/
abbrev cuspForm_102_eta_2p2_3p1_6m1_17m1_34p1_51p2_old_408_1 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_102_eta_2p2_3p1_6m1_17m1_34p1_51p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_102_eta_2p2_3p1_6m1_17m1_34p1_51p2_old_408_1_eq_eta :
    cuspForm_102_eta_2p2_3p1_6m1_17m1_34p1_51p2_old_408_1 =
      etaQuotientCuspForm 408 sparse![408; 1 => 2, 2 => 1, 5 => -1, 16 => -1, 33 => 1, 50 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_2p2_3p1_6m1_17m1_34p1_51p2_old_408_1_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_2p2_3p1_6m1_17m1_34p1_51p2_old_408_1 =
    [0, 0, 0, 0, 0, 1, 0, -2, -1, -1, 2, 2, 1, 1, -3, 2, 1, -1, -1, -2,
     -1, -3, 2, 1, -1, -1, 0, 3, 2, 3, 2, -4, 2, 2, -1, -1, -3, 0, -3, 2,
     -2, 0, -4, -3, 4, 0, 4, 1, -2, 5, 2, -1, 0, -5, 3, -4, 1, -1, 2, -2,
     -3, 4, -1, 6, 0, -2, 1, 3, 0, -1, -3, 3, -2, 0, -3, 0, -5, -4, 2, 0,
     5, -1, -2, 0, 5, 0, -2, 1, 4, -3, 1, 0, -1, -5, -3, 2, 4, 6, 7, -7] := by
  eta_coeff

end WeightTwoCusps
