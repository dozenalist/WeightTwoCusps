module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«40».New.«40_eta_1m2_2p5_4m1_5p2_10m1_20p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(2z)^(-2) η(4z)^5 η(8z)^(-1) η(10z)^2 η(20z)^(-1) η(40z)`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^5 η(8z)^(-1) η(10z)^2 η(20z)^(-1) η(40z)` at level 320. -/
abbrev cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_320_2 : gamma0CuspForms 320 :=
  gamma0RescaleToLevel cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_320_2_eq_eta :
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_320_2 =
      etaQuotientCuspForm 320 sparse![320; 1 => -2, 3 => 5, 7 => -1, 9 => 2, 19 => -1, 39 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_320_2_first_coeffs :
    first_coeffs 100 cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_320_2 =
    [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, -4, 0, -4, 0, 0, 0, -3, 0,
     -2, 0, 4, 0, 0, 0, -2, 0, 4, 0, 0, 0, 0, 0, 2, 0, 2, 0, 4, 0,
     0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, -2, 0,
     4, 0, -8, 0, 0, 0, 0, 0, -12, 0, -4, 0, 0, 0, 6, 0, -8, 0, 0, 0,
     0, 0, -6, 0, -8, 0, -8, 0, 0, 0, -3, 0, 12, 0, 4, 0, 0, 0, 9, 0] := by
  eta_coeff

end WeightTwoCusps
