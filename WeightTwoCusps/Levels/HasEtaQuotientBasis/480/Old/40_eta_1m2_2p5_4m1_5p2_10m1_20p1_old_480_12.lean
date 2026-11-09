module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«40».New.«40_eta_1m2_2p5_4m1_5p2_10m1_20p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(12z)^(-2) η(24z)^5 η(48z)^(-1) η(60z)^2 η(120z)^(-1) η(240z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(12z)` of `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(12z)^(-2) η(24z)^5 η(48z)^(-1) η(60z)^2 η(120z)^(-1) η(240z)` at level 480. -/
abbrev cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_480_12 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1 12

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_480_12_eq_eta :
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_480_12 =
      etaQuotientCuspForm 480 sparse![480; 11 => -2, 23 => 5, 47 => -1, 59 => 2, 119 => -1, 239 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_480_12_first_coeffs :
    first_coeffs 100 cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_480_12 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
