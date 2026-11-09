module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«198».New.«198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-2) η(11z) η(18z)^2 η(22z)^(-1) η(33z)^(-1) η(66z)^3 η(99z) η(198z)^(-1)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-2) η(11z) η(18z)^2 η(22z)^(-1) η(33z)^(-1) η(66z)^3 η(99z) η(198z)^(-1)` at level 396. -/
abbrev cuspForm_198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1_old_396_1 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1_old_396_1_eq_eta :
    cuspForm_198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1_old_396_1 =
      etaQuotientCuspForm 396 sparse![396; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 10 => 1, 17 => 2, 21 => -1, 32 => -1, 65 => 3, 98 => 1, 197 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1_old_396_1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1_old_396_1 =
    [0, 0, 0, 1, 2, 3, 1, -1, -1, 0, 3, 0, 1, -1, 0, 1, -3, 1, -2, 2,
     -2, -5, 0, -1, 3, -4, -4, -1, -1, 4, -1, 2, 2, 0, -1, -5, 2, 2, 0, 1,
     -1, 1, -1, -2, 0, -3, 1, -2, -3, 1, 1, 0, -3, 0, 3, 0, 2, 2, 2, 1,
     -3, -3, -1, 3, 2, -4, 0, 3, 1, -3, -9, -5, -4, 4, 1, 1, -4, 0, -3, -1,
     4, 2, 7, -5, 3, 0, 4, 8, -1, 3, -3, 8, 8, 4, 3, -7, -1, -4, 5, 1] := by
  eta_coeff

end WeightTwoCusps
