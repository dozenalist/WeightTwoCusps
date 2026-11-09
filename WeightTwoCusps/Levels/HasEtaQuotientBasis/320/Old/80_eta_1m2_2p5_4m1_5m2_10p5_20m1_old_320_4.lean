module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m2_2p5_4m1_5m2_10p5_20m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(4z)^(-2) η(8z)^5 η(16z)^(-1) η(20z)^(-2) η(40z)^5 η(80z)^(-1)`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z)^5 η(16z)^(-1) η(20z)^(-2) η(40z)^5 η(80z)^(-1)` at level 320. -/
abbrev cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_320_4 : gamma0CuspForms 320 :=
  gamma0Rescale cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_320_4_eq_eta :
    cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_320_4 =
      etaQuotientCuspForm 320 sparse![320; 3 => -2, 7 => 5, 15 => -1, 19 => -2, 39 => 5, 79 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_320_4_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_320_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0,
     2, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -8, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -6, 0, 0, 0, -4, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
