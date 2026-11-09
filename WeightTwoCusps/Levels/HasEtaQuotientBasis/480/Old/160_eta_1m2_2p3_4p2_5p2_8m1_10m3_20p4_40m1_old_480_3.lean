module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«160».New.«160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(3z)^(-2) η(6z)^3 η(12z)^2 η(15z)^2 η(24z)^(-1) η(30z)^(-3) η(60z)^4 η(120z)^(-1)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^3 η(12z)^2 η(15z)^2 η(24z)^(-1) η(30z)^(-3) η(60z)^4 η(120z)^(-1)` at level 480. -/
abbrev cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1_old_480_3 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1_old_480_3_eq_eta :
    cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1_old_480_3 =
      etaQuotientCuspForm 480 sparse![480; 2 => -2, 5 => 3, 11 => 2, 14 => 2, 23 => -1, 29 => -3, 59 => 4, 119 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1_old_480_3_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_1m2_2p3_4p2_5p2_8m1_10m3_20p4_40m1_old_480_3 =
    [0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0,
     0, 2, 0, 0, 0, 0, 0, -3, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 6,
     0, 0, 8, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, -6, 0, 0, -8, 0, 0,
     4, 0, 0, 0, 0, 0, -8, 0, 0, 6, 0, 0, 0, 0, 0, -11, 0, 0, -4, 0,
     0, -4, 0, 0, -16, 0, 0, -10, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
