module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«102».New.«102_eta_1m1_2p3_3p1_6m1_17p1_34m1_51m1_102p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 204

The eta expression is `η(z)^(-1) η(2z)^3 η(3z) η(6z)^(-1) η(17z) η(34z)^(-1) η(51z)^(-1) η(102z)^3`; see
[the local level table](../../TABLE.md#level-204).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_102_eta_1m1_2p3_3p1_6m1_17p1_34m1_51m1_102p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(3z) η(6z)^(-1) η(17z) η(34z)^(-1) η(51z)^(-1) η(102z)^3` at level 204. -/
abbrev cuspForm_102_eta_1m1_2p3_3p1_6m1_17p1_34m1_51m1_102p3_old_204_1 : gamma0CuspForms 204 :=
  gamma0RescaleToLevel cuspForm_102_eta_1m1_2p3_3p1_6m1_17p1_34m1_51m1_102p3 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_102_eta_1m1_2p3_3p1_6m1_17p1_34m1_51m1_102p3_old_204_1_eq_eta :
    cuspForm_102_eta_1m1_2p3_3p1_6m1_17p1_34m1_51m1_102p3_old_204_1 =
      etaQuotientCuspForm 204 sparse![204; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 16 => 1, 33 => -1, 50 => -1, 101 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1m1_2p3_3p1_6m1_17p1_34m1_51m1_102p3_old_204_1_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1m1_2p3_3p1_6m1_17p1_34m1_51m1_102p3_old_204_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1, -2, -1, 1, 0, 1, -2,
     1, 3, 0, 2, 0, 1, -1, -1, -1, -1, 2, 2, 1, -3, -1, -1, 1, -2, -2, -1,
     -4, -1, -1, 3, 1, 1, 4, -1, -2, 3, 1, 1, 0, 1, 2, 0, 4, 2, 0, 0,
     0, -2, 0, -4, 0, 1, -4, 1, 0, 1, -3, -3, -1, -2, -1, 1, -1, -2, 1, 0,
     1, -1, 1, 0, 0, 0, -1, 4, 1, 1, 0, -2, 0, 3, 1, 1, -1, 2, 5, 4] := by
  eta_coeff

end WeightTwoCusps
