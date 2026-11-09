module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«225».New.«225_eta_3p1_9m1_45p4_75p1_225m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(6z) η(18z)^(-1) η(90z)^4 η(150z) η(450z)^(-1)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(18z)^(-1) η(90z)^4 η(150z) η(450z)^(-1)` at level 450. -/
abbrev cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_old_450_2 : gamma0CuspForms 450 :=
  gamma0Rescale cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_old_450_2_eq_eta :
    cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_old_450_2 =
      etaQuotientCuspForm 450 sparse![450; 5 => 1, 17 => -1, 89 => 4, 149 => 1, 449 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_old_450_2_first_coeffs :
    first_coeffs 100 cuspForm_225_eta_3p1_9m1_45p4_75p1_225m1_old_450_2 =
    [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 3, 0, 0, 0,
     0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0,
     -3, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
