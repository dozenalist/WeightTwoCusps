module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«40».New.«40_eta_1m2_2p5_4m1_5p2_10m1_20p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(7z)^(-2) η(14z)^5 η(28z)^(-1) η(35z)^2 η(70z)^(-1) η(140z)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(7z)^(-2) η(14z)^5 η(28z)^(-1) η(35z)^2 η(70z)^(-1) η(140z)` at level 280. -/
abbrev cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_280_7 : gamma0CuspForms 280 :=
  gamma0Rescale cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1 7

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_280_7_eq_eta :
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_280_7 =
      etaQuotientCuspForm 280 sparse![280; 6 => -2, 13 => 5, 27 => -1, 34 => 2, 69 => -1, 139 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_280_7_first_coeffs :
    first_coeffs 100 cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_280_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     0, 0, -4, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, -3, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 4, 0] := by
  eta_coeff

end WeightTwoCusps
