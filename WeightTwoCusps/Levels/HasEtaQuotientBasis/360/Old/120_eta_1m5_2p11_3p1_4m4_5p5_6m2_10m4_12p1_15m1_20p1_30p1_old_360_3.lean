module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«120».New.«120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(3z)^(-5) η(6z)^11 η(9z) η(12z)^(-4) η(15z)^5 η(18z)^(-2) η(30z)^(-4) η(36z) η(45z)^(-1) η(60z) η(90z)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-5) η(6z)^11 η(9z) η(12z)^(-4) η(15z)^5 η(18z)^(-2) η(30z)^(-4) η(36z) η(45z)^(-1) η(60z) η(90z)` at level 360. -/
abbrev cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_360_3 : gamma0CuspForms 360 :=
  gamma0Rescale cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_360_3_eq_eta :
    cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_360_3 =
      etaQuotientCuspForm 360 sparse![360; 2 => -5, 5 => 11, 8 => 1, 11 => -4, 14 => 5, 17 => -2, 29 => -4, 35 => 1, 44 => -1, 59 => 1, 89 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_360_3_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_360_3 =
    [0, 0, 0, 1, 0, 0, 5, 0, 0, 9, 0, 0, 9, 0, 0, 13, 0, 0, 17, 0,
     0, 2, 0, 0, -9, 0, 0, 3, 0, 0, -5, 0, 0, -20, 0, 0, 9, 0, 0, 22,
     0, 0, -8, 0, 0, -3, 0, 0, 9, 0, 0, -22, 0, 0, -31, 0, 0, -8, 0, 0,
     -9, 0, 0, -18, 0, 0, 0, 0, 0, 10, 0, 0, -9, 0, 0, -11, 0, 0, 10, 0,
     0, -9, 0, 0, -36, 0, 0, -14, 0, 0, -17, 0, 0, -32, 0, 0, -9, 0, 0, 12] := by
  eta_coeff

end WeightTwoCusps
