module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«200».New.«200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(2z)^(-2) η(4z)^5 η(8z)^(-2) η(10z)^2 η(20z)^(-1) η(40z) η(200z)`; see
[the local level table](../../TABLE.md#level-400).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^5 η(8z)^(-2) η(10z)^2 η(20z)^(-1) η(40z) η(200z)` at level 400. -/
abbrev cuspForm_200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1_old_400_2 : gamma0CuspForms 400 :=
  gamma0Rescale cuspForm_200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1_old_400_2_eq_eta :
    cuspForm_200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1_old_400_2 =
      etaQuotientCuspForm 400 sparse![400; 1 => -2, 3 => 5, 7 => -2, 9 => 2, 19 => -1, 39 => 1, 199 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1_old_400_2_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1_old_400_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0,
     -2, 0, -4, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, -2, 0, 0, 0, 0, 0, 2, 0,
     4, 0, 4, 0, 0, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, 0, 0, 4, 0,
     0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -3, 0, -6, 0, 0, 0, 0, 0, -6, 0] := by
  eta_coeff

end WeightTwoCusps
