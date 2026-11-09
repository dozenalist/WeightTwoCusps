module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«200».New.«200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(2z)^(-2) η(4z)^4 η(8z)^(-1) η(10z)^3 η(20z)^(-1) η(50z)^(-1) η(100z) η(200z)`; see
[the local level table](../../TABLE.md#level-400).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^4 η(8z)^(-1) η(10z)^3 η(20z)^(-1) η(50z)^(-1) η(100z) η(200z)` at level 400. -/
abbrev cuspForm_200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1_old_400_1 : gamma0CuspForms 400 :=
  gamma0RescaleToLevel cuspForm_200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1_old_400_1_eq_eta :
    cuspForm_200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1_old_400_1 =
      etaQuotientCuspForm 400 sparse![400; 1 => -2, 3 => 4, 7 => -1, 9 => 3, 19 => -1, 49 => -1, 99 => 1, 199 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1_old_400_1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1_old_400_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3,
     0, -1, 0, -2, 0, 1, 0, -2, 0, -3, 0, 2, 0, -2, 0, -3, 0, 0, 0, -4,
     0, -3, 0, 0, 0, -2, 0, -2, 0, 1, 0, -5, 0, 0, 0, 2, 0, -4, 0, 2,
     0, 4, 0, 4, 0, -2, 0, 6, 0, 5, 0, 0, 0, 0, 0, -1, 0, -2, 0, -6,
     0, 7, 0, -2, 0, 4, 0, 6, 0, 0, 0, -2, 0, -6, 0, 4, 0, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
