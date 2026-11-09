module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«100».New.«100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 200

The eta expression is `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z)^2 η(20z)^2 η(25z)^(-1) η(50z)^2 η(100z)^(-1)`; see
[the local level table](../../TABLE.md#level-200).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z)^2 η(20z)^2 η(25z)^(-1) η(50z)^2 η(100z)^(-1)` at level 200. -/
abbrev cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1_old_200_1 : gamma0CuspForms 200 :=
  gamma0RescaleToLevel cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1_old_200_1_eq_eta :
    cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1_old_200_1 =
      etaQuotientCuspForm 200 sparse![200; 0 => -1, 1 => 2, 3 => -1, 4 => 2, 19 => 2, 24 => -1, 49 => 2, 99 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1_old_200_1_first_coeffs :
    first_coeffs 100 cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1_old_200_1 =
    [0, 1, 1, 0, 1, 1, -1, -1, 1, 0, 0, -1, -1, 1, -2, -2, 1, 2, -2, -1,
     0, -2, -3, -3, -1, -1, 4, 1, -2, 4, 0, -2, 1, 1, 3, 2, -2, -1, 5, -4,
     0, 3, 2, 3, -3, 1, -6, -3, -1, -3, 0, 7, 4, -1, 5, 0, -2, -3, 0, 8,
     0, 2, 2, 1, 1, 2, 3, 4, 3, -6, 0, -4, -2, -4, -2, 2, 5, 2, -4, 2,
     0, -7, -3, 2, 2, -6, 4, 2, -3, 1, 0, 0, -6, -2, -12, -4, -1, -1, -3, 2] := by
  eta_coeff

end WeightTwoCusps
