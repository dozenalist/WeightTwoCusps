module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«240».New.«240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(2z)^(-4) η(4z)^8 η(6z)^2 η(8z)^(-2) η(10z)^2 η(12z)^(-3) η(20z)^(-1) η(24z) η(40z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-4) η(4z)^8 η(6z)^2 η(8z)^(-2) η(10z)^2 η(12z)^(-3) η(20z)^(-1) η(24z) η(40z)` at level 480. -/
abbrev cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1_old_480_2 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1_old_480_2_eq_eta :
    cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1_old_480_2 =
      etaQuotientCuspForm 480 sparse![480; 1 => -4, 3 => 8, 5 => 2, 7 => -2, 9 => 2, 11 => -3, 19 => -1, 23 => 1, 39 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1_old_480_2_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1_old_480_2 =
    [0, 0, 1, 0, 4, 0, 6, 0, 6, 0, 7, 0, 6, 0, 4, 0, 6, 0, 9, 0,
     10, 0, 8, 0, 6, 0, 4, 0, 2, 0, 6, 0, 12, 0, 8, 0, 0, 0, 2, 0,
     0, 0, 0, 0, 4, 0, 2, 0, 0, 0, -11, 0, -8, 0, 0, 0, 0, 0, -2, 0,
     -6, 0, -10, 0, -18, 0, -6, 0, -4, 0, -8, 0, -18, 0, -12, 0, 4, 0, -12, 0,
     0, 0, 0, 0, -12, 0, -22, 0, -12, 0, 3, 0, -14, 0, -10, 0, -18, 0, -21, 0] := by
  eta_coeff

end WeightTwoCusps
