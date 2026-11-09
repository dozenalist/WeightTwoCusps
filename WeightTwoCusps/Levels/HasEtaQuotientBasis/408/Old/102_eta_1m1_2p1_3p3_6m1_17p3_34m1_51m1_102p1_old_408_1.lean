module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«102».New.«102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(z)^(-1) η(2z) η(3z)^3 η(6z)^(-1) η(17z)^3 η(34z)^(-1) η(51z)^(-1) η(102z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^3 η(6z)^(-1) η(17z)^3 η(34z)^(-1) η(51z)^(-1) η(102z)` at level 408. -/
abbrev cuspForm_102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1_old_408_1 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1_old_408_1_eq_eta :
    cuspForm_102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1_old_408_1 =
      etaQuotientCuspForm 408 sparse![408; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 16 => 3, 33 => -1, 50 => -1, 101 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1_old_408_1_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1m1_2p1_3p3_6m1_17p3_34m1_51m1_102p1_old_408_1 =
    [0, 0, 0, 1, 1, 1, -1, -1, 0, -1, 0, -2, 0, -1, -1, 1, -1, 0, 1, 1,
     -2, -5, -3, 4, 3, 3, 4, 0, 5, 2, 4, 3, -4, 4, 0, -4, -2, -2, 8, 1,
     -4, -3, -9, -3, -1, 1, -7, -4, -2, 2, -4, -1, 4, -2, 4, -3, 3, -3, 4, 4,
     -6, 2, -7, 3, -1, -1, 7, -2, 3, 4, 4, 3, -3, 0, 6, -2, 6, 8, 2, -3,
     12, 4, 4, -4, 5, -1, -10, 2, -3, 4, -4, 2, -11, -1, 2, -1, 7, -10, -10, -8] := by
  eta_coeff

end WeightTwoCusps
