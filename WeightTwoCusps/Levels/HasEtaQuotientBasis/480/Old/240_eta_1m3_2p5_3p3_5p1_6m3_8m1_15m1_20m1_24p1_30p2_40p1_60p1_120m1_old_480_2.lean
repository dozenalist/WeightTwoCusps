module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«240».New.«240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(2z)^(-3) η(4z)^5 η(6z)^3 η(10z) η(12z)^(-3) η(16z)^(-1) η(30z)^(-1) η(40z)^(-1) η(48z) η(60z)^2 η(80z) η(120z) η(240z)^(-1)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^5 η(6z)^3 η(10z) η(12z)^(-3) η(16z)^(-1) η(30z)^(-1) η(40z)^(-1) η(48z) η(60z)^2 η(80z) η(120z) η(240z)^(-1)` at level 480. -/
abbrev cuspForm_240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1_old_480_2 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1_old_480_2_eq_eta :
    cuspForm_240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1_old_480_2 =
      etaQuotientCuspForm 480 sparse![480; 1 => -3, 3 => 5, 5 => 3, 9 => 1, 11 => -3, 15 => -1, 29 => -1, 39 => -1, 47 => 1, 59 => 2, 79 => 1, 119 => 1, 239 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1_old_480_2_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m3_2p5_3p3_5p1_6m3_8m1_15m1_20m1_24p1_30p2_40p1_60p1_120m1_old_480_2 =
    [0, 0, 1, 0, 3, 0, 4, 0, 4, 0, 2, 0, 0, 0, 0, 0, 1, 0, 5, 0,
     4, 0, 0, 0, -3, 0, -6, 0, -2, 0, 3, 0, 8, 0, 6, 0, -1, 0, -4, 0,
     -1, 0, 4, 0, 6, 0, 8, 0, -2, 0, -5, 0, -4, 0, 0, 0, 6, 0, -2, 0,
     -3, 0, -8, 0, -11, 0, -4, 0, 0, 0, 0, 0, -4, 0, -6, 0, 0, 0, 0, 0,
     2, 0, 6, 0, 2, 0, -4, 0, -6, 0, -2, 0, -8, 0, -8, 0, -7, 0, -3, 0] := by
  eta_coeff

end WeightTwoCusps
