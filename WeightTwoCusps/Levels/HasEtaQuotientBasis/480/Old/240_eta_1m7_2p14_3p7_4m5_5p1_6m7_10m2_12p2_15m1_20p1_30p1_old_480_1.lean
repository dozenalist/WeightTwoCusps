module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«240».New.«240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(z)^(-7) η(2z)^14 η(3z)^7 η(4z)^(-5) η(5z) η(6z)^(-7) η(10z)^(-2) η(12z)^2 η(15z)^(-1) η(20z) η(30z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-7) η(2z)^14 η(3z)^7 η(4z)^(-5) η(5z) η(6z)^(-7) η(10z)^(-2) η(12z)^2 η(15z)^(-1) η(20z) η(30z)` at level 480. -/
abbrev cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1_old_480_1 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1_old_480_1_eq_eta :
    cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1_old_480_1 =
      etaQuotientCuspForm 480 sparse![480; 0 => -7, 1 => 14, 2 => 7, 3 => -5, 4 => 1, 5 => -7, 9 => -2, 11 => 2, 14 => -1, 19 => 1, 29 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1_old_480_1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m7_2p14_3p7_4m5_5p1_6m7_10m2_12p2_15m1_20p1_30p1_old_480_1 =
    [0, 1, 7, 21, 35, 33, 13, 0, 15, 41, 51, 36, 5, -22, -20, 33, 75, 42, -13, -36,
     -5, 20, 28, 48, -15, -51, -14, 21, 40, -34, -31, -48, -105, -4, 14, -20, -85, -94, 12, -22,
     15, 54, -60, -104, -60, 13, 4, -80, -75, -67, -97, 2, 10, -62, -47, -52, 0, -36, 2, 76,
     -35, -22, -24, -20, -45, -46, 52, -56, -90, -52, -20, -8, 15, 90, 42, -31, -20, 40, -26, 48,
     75, -19, -42, -96, 40, 26, -32, 6, -60, -6, 31, 40, 120, 72, 20, 92, 105, 42, 31, -4] := by
  eta_coeff

end WeightTwoCusps
