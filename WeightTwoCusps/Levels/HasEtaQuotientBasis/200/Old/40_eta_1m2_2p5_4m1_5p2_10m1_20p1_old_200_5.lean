module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«40».New.«40_eta_1m2_2p5_4m1_5p2_10m1_20p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 200

The eta expression is `η(5z)^(-2) η(10z)^5 η(20z)^(-1) η(25z)^2 η(50z)^(-1) η(100z)`; see
[the local level table](../../TABLE.md#level-200).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-2) η(10z)^5 η(20z)^(-1) η(25z)^2 η(50z)^(-1) η(100z)` at level 200. -/
abbrev cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_200_5 : gamma0CuspForms 200 :=
  gamma0Rescale cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_200_5_eq_eta :
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_200_5 =
      etaQuotientCuspForm 200 sparse![200; 4 => -2, 9 => 5, 19 => -1, 24 => 2, 49 => -1, 99 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_200_5_first_coeffs :
    first_coeffs 100 cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_200_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -3, 0, 0, 0, 0, -2, 0, 0, 0, 0, 4, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
