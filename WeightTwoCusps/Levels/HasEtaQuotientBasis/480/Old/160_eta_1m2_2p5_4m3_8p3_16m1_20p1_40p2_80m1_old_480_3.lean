module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«160».New.«160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(3z)^(-2) η(6z)^5 η(12z)^(-3) η(24z)^3 η(48z)^(-1) η(60z) η(120z)^2 η(240z)^(-1)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^5 η(12z)^(-3) η(24z)^3 η(48z)^(-1) η(60z) η(120z)^2 η(240z)^(-1)` at level 480. -/
abbrev cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_old_480_3 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_old_480_3_eq_eta :
    cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_old_480_3 =
      etaQuotientCuspForm 480 sparse![480; 2 => -2, 5 => 5, 11 => -3, 23 => 3, 47 => -1, 59 => 1, 119 => 2, 239 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_old_480_3_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_old_480_3 =
    [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0,
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
