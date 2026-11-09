module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«198».New.«198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(9z)^(-1) η(11z)^(-1) η(18z) η(22z) η(33z)^2 η(66z)^(-1) η(99z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(9z)^(-1) η(11z)^(-1) η(18z) η(22z) η(33z)^2 η(66z)^(-1) η(99z)` at level 396. -/
abbrev cuspForm_198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1_old_396_1 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1_old_396_1_eq_eta :
    cuspForm_198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1_old_396_1 =
      etaQuotientCuspForm 396 sparse![396; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 8 => -1, 10 => -1, 17 => 1, 21 => 1, 32 => 2, 65 => -1, 98 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1_old_396_1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1_old_396_1 =
    [0, 0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -2, 0, 0, 4, 2, -1,
     0, -2, 0, -2, 0, -3, -1, 1, 2, 1, -2, 1, -2, 0, -1, 0, -6, -2, -1, 0,
     0, -3, 3, -3, 0, -2, -1, -5, -3, -3, -2, 2, 1, 2, -2, 1, 2, 2, -5, -1,
     -3, 3, 8, 2, 0, -1, 1, 2, 4, -2, 1, -6, 4, 6, -3, 3, -1, 1, -3, 2,
     0, 1, 2, 4, 4, -2, 3, 2, 0, 2, 4, -5, 1, -3, 7, 1, -2, 6, -2, 0] := by
  eta_coeff

end WeightTwoCusps
