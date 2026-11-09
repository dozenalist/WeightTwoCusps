module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«195».New.«195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z)^2 η(3z)^(-1) η(5z)^(-1) η(13z)^(-1) η(15z)^2 η(39z)^2 η(65z)^2 η(195z)^(-1)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(3z)^(-1) η(5z)^(-1) η(13z)^(-1) η(15z)^2 η(39z)^2 η(65z)^2 η(195z)^(-1)` at level 390. -/
abbrev cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_old_390_1 : gamma0CuspForms 390 :=
  gamma0RescaleToLevel cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_old_390_1_eq_eta :
    cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_old_390_1 =
      etaQuotientCuspForm 390 sparse![390; 0 => 2, 2 => -1, 4 => -1, 12 => -1, 14 => 2, 38 => 2, 64 => 2, 194 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_old_390_1_first_coeffs :
    first_coeffs 100 cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_old_390_1 =
    [0, 1, -2, -1, 3, -1, 2, 0, -4, 1, 2, 0, -3, 0, 1, -1, 4, 1, -3, 4,
     -3, -4, 1, 0, 4, -2, 0, 1, -3, 3, 2, -2, 0, -3, -4, 2, 5, 4, -9, 0,
     4, 0, 9, -3, -3, -1, -2, -2, -4, 2, 6, -3, 0, 3, -3, 2, 3, -3, -5, 1,
     -3, 0, 7, 2, -7, 0, 6, 3, 8, -3, -7, 0, -5, -1, -7, -4, 14, 7, 0, 1,
     -4, -2, 0, -4, -13, -1, 8, 1, 3, 8, 1, 0, 5, -3, 3, -4, 0, -5, -2, 1] := by
  eta_coeff

end WeightTwoCusps
