module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«160».New.«160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(z)^(-2) η(2z)^3 η(4z)^2 η(5z)^2 η(8z)^(-1) η(10z)^(-3) η(20z)^4 η(40z)^(-1)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(4z)^2 η(5z)^2 η(8z)^(-1) η(10z)^(-3) η(20z)^4 η(40z)^(-1)` at level 480. -/
abbrev cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1_old_480_1 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1_old_480_1_eq_eta :
    cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1_old_480_1 =
      etaQuotientCuspForm 480 sparse![480; 0 => -2, 1 => 3, 3 => 2, 4 => 2, 7 => -1, 9 => -3, 19 => 4, 39 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1_old_480_1_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1_old_480_1 =
    [0, 1, 2, 2, 4, 3, 0, 2, 0, -3, 2, 4, 0, 6, 8, -2, 0, 2, -6, -8,
     4, 0, -8, 6, 0, -11, -4, -4, -16, -10, 0, -4, 0, 0, 4, -2, -12, -2, -8, -12,
     0, 10, 0, 2, 16, -9, -8, 2, 0, -7, 2, 4, -8, 14, 0, -4, 0, 0, -4, 0,
     0, -10, 16, 2, 0, 18, 0, 6, 8, 0, 8, 12, 0, -6, 12, 2, 16, 0, 0, 8,
     0, 9, -12, 10, 0, 6, 16, -4, 0, 10, -6, -12, 16, 0, -8, 8, 0, 18, 18, 4] := by
  eta_coeff

end WeightTwoCusps
