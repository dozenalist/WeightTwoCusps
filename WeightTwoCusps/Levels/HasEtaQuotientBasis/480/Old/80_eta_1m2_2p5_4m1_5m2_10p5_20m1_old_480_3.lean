module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m2_2p5_4m1_5m2_10p5_20m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(3z)^(-2) η(6z)^5 η(12z)^(-1) η(15z)^(-2) η(30z)^5 η(60z)^(-1)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^5 η(12z)^(-1) η(15z)^(-2) η(30z)^5 η(60z)^(-1)` at level 480. -/
abbrev cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_480_3 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_480_3_eq_eta :
    cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_480_3 =
      etaQuotientCuspForm 480 sparse![480; 2 => -2, 5 => 5, 11 => -1, 14 => -2, 29 => 5, 59 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_480_3_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_480_3 =
    [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     0, 4, 0, 0, 0, 0, 0, -3, 0, 0, 2, 0, 0, -4, 0, 0, 0, 0, 0, -2,
     0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -6, 0, 0, -4, 0, 0,
     0, 0, 0, 0, 0, 0, 8, 0, 0, -4, 0, 0, 0, 0, 0, 1, 0, 0, -4, 0,
     0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
