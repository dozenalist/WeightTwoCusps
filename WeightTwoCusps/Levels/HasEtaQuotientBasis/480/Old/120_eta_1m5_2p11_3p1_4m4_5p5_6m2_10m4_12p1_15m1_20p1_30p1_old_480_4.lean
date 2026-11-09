module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«120».New.«120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(4z)^(-5) η(8z)^11 η(12z) η(16z)^(-4) η(20z)^5 η(24z)^(-2) η(40z)^(-4) η(48z) η(60z)^(-1) η(80z) η(120z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-5) η(8z)^11 η(12z) η(16z)^(-4) η(20z)^5 η(24z)^(-2) η(40z)^(-4) η(48z) η(60z)^(-1) η(80z) η(120z)` at level 480. -/
abbrev cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_480_4 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_480_4_eq_eta :
    cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_480_4 =
      etaQuotientCuspForm 480 sparse![480; 3 => -5, 7 => 11, 11 => 1, 15 => -4, 19 => 5, 23 => -2, 39 => -4, 47 => 1, 59 => -1, 79 => 1, 119 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_480_4_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m5_2p11_3p1_4m4_5p5_6m2_10m4_12p1_15m1_20p1_30p1_old_480_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 9, 0, 0, 0, 9, 0, 0, 0,
     13, 0, 0, 0, 17, 0, 0, 0, 2, 0, 0, 0, -9, 0, 0, 0, 3, 0, 0, 0,
     -5, 0, 0, 0, -20, 0, 0, 0, 9, 0, 0, 0, 22, 0, 0, 0, -8, 0, 0, 0,
     -3, 0, 0, 0, 9, 0, 0, 0, -22, 0, 0, 0, -31, 0, 0, 0, -8, 0, 0, 0,
     -9, 0, 0, 0, -18, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, -9, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
