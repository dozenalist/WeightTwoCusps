module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«240».New.«240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(z)^(-4) η(2z)^8 η(3z)^2 η(4z)^(-2) η(5z)^2 η(6z)^(-3) η(10z)^(-1) η(12z) η(20z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^2 η(4z)^(-2) η(5z)^2 η(6z)^(-3) η(10z)^(-1) η(12z) η(20z)` at level 480. -/
abbrev cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1_old_480_1 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1_old_480_1_eq_eta :
    cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1_old_480_1 =
      etaQuotientCuspForm 480 sparse![480; 0 => -4, 1 => 8, 2 => 2, 3 => -2, 4 => 2, 5 => -3, 9 => -1, 11 => 1, 19 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1_old_480_1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m4_2p8_3p2_4m2_5p2_6m3_10m1_12p1_20p1_old_480_1 =
    [0, 1, 4, 6, 6, 7, 6, 4, 6, 9, 10, 8, 6, 4, 2, 6, 12, 8, 0, 2,
     0, 0, 4, 2, 0, -11, -8, 0, 0, -2, -6, -10, -18, -6, -4, -8, -18, -12, 4, -12,
     0, 0, -12, -22, -12, 3, -14, -10, -18, -21, -20, -6, 0, -24, -12, -10, -12, -12, -8, 4,
     -12, -8, -8, 0, -12, -14, 12, -14, 0, -12, -10, 0, 6, 30, 0, -6, 0, 8, -12, 18,
     18, -9, 0, -14, 12, 2, -2, 6, -12, 6, 6, -8, 12, 24, 22, 14, 24, 10, 12, 0] := by
  eta_coeff

end WeightTwoCusps
