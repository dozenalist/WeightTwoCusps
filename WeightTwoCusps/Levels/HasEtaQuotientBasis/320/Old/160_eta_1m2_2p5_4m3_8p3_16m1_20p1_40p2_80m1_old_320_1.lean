module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«160».New.«160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-3) η(8z)^3 η(16z)^(-1) η(20z) η(40z)^2 η(80z)^(-1)`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-3) η(8z)^3 η(16z)^(-1) η(20z) η(40z)^2 η(80z)^(-1)` at level 320. -/
abbrev cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_old_320_1 : gamma0CuspForms 320 :=
  gamma0RescaleToLevel cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_old_320_1_eq_eta :
    cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_old_320_1 =
      etaQuotientCuspForm 320 sparse![320; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 15 => -1, 19 => 1, 39 => 2, 79 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_old_320_1_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_1m2_2p5_4m3_8p3_16m1_20p1_40p2_80m1_old_320_1 =
    [0, 1, 2, 0, 0, 3, 2, 0, 0, 1, 0, 0, 0, -2, 2, 0, 0, 2, -2, 0,
     0, 0, -4, 0, 0, -7, 0, 0, 0, -2, -2, 0, 0, 0, -4, 0, 0, -2, 0, 0,
     0, -2, -4, 0, 0, -9, -10, 0, 0, -3, 2, 0, 0, 6, -4, 0, 0, -8, 4, 0,
     0, -2, 12, 0, 0, 22, 0, 0, 0, 8, 6, 0, 0, 2, 8, 0, 0, 8, 4, 0,
     0, -3, 0, 0, 0, 6, 18, 0, 0, 2, -4, 0, 0, 0, 2, 0, 0, 10, 6, 0] := by
  eta_coeff

end WeightTwoCusps
