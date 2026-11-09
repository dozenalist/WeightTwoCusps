module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«225».New.«225_eta_1m1_3p1_5p4_25m1_75p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(2z)^(-1) η(6z) η(10z)^4 η(50z)^(-1) η(150z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(6z) η(10z)^4 η(50z)^(-1) η(150z)` at level 450. -/
abbrev cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_old_450_2 : gamma0CuspForms 450 :=
  gamma0Rescale cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_old_450_2_eq_eta :
    cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_old_450_2 =
      etaQuotientCuspForm 450 sparse![450; 1 => -1, 5 => 1, 9 => 4, 49 => -1, 149 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_old_450_2_first_coeffs :
    first_coeffs 100 cuspForm_225_eta_1m1_3p1_5p4_25m1_75p1_old_450_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 4, 0, 1, 0, 3, 0,
     1, 0, 5, 0, 0, 0, 4, 0, 1, 0, 4, 0, -4, 0, 1, 0, 0, 0, 3, 0,
     -2, 0, 1, 0, -1, 0, 1, 0, -8, 0, -1, 0, -3, 0, 1, 0, -7, 0, 1, 0,
     -4, 0, 5, 0, -3, 0, -2, 0, -1, 0, 0, 0, -2, 0, -6, 0, -3, 0, 5, 0,
     -3, 0, -12, 0, -2, 0, 3, 0, -6, 0, -4, 0, 1, 0, 3, 0, -2, 0, -18, 0] := by
  eta_coeff

end WeightTwoCusps
