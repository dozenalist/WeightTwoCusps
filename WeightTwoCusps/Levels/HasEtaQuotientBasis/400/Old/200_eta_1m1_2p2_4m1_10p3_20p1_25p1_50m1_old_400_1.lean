module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«200».New.«200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(10z)^3 η(20z) η(25z) η(50z)^(-1)`; see
[the local level table](../../TABLE.md#level-400).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(10z)^3 η(20z) η(25z) η(50z)^(-1)` at level 400. -/
abbrev cuspForm_200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1_old_400_1 : gamma0CuspForms 400 :=
  gamma0RescaleToLevel cuspForm_200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1_old_400_1_eq_eta :
    cuspForm_200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1_old_400_1 =
      etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 2, 3 => -1, 9 => 3, 19 => 1, 24 => 1, 49 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1_old_400_1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_1m1_2p2_4m1_10p3_20p1_25p1_50m1_old_400_1 =
    [0, 1, 1, 0, 1, 1, 1, 1, 1, 2, 2, -1, -1, 3, 0, 0, 1, 2, 2, -1,
     0, 0, 1, -1, -1, 1, -2, -5, -2, -2, -4, 2, 1, -5, 1, -4, -2, 1, -7, 0,
     0, -1, -6, -3, -3, -3, 0, -1, -1, -1, -2, -5, 4, 1, -3, 4, -2, -5, 8, -4,
     0, -2, -6, 7, 1, -2, -1, 8, 3, 0, 4, 0, -2, 4, 0, 0, 5, -6, -4, 10,
     0, -1, 9, -6, 2, 2, 2, 10, -3, -1, 2, 8, -6, -10, 6, 4, -1, 1, -3, -2] := by
  eta_coeff

end WeightTwoCusps
