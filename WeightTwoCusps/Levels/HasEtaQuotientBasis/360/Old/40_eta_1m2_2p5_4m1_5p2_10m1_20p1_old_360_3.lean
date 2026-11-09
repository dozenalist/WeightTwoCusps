module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«40».New.«40_eta_1m2_2p5_4m1_5p2_10m1_20p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 360

The eta expression is `η(3z)^(-2) η(6z)^5 η(12z)^(-1) η(15z)^2 η(30z)^(-1) η(60z)`; see
[the local level table](../../TABLE.md#level-360).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^5 η(12z)^(-1) η(15z)^2 η(30z)^(-1) η(60z)` at level 360. -/
abbrev cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_360_3 : gamma0CuspForms 360 :=
  gamma0RescaleToLevel cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_360_3_eq_eta :
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_360_3 =
      etaQuotientCuspForm 360 sparse![360; 2 => -2, 5 => 5, 11 => -1, 14 => 2, 29 => -1, 59 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_360_3_first_coeffs :
    first_coeffs 100 cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_360_3 =
    [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4, 0,
     0, -4, 0, 0, 0, 0, 0, -3, 0, 0, -2, 0, 0, 4, 0, 0, 0, 0, 0, -2,
     0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0,
     0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 4, 0, 0, -8, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
