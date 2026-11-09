module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«195».New.«195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(2z)^2 η(6z)^(-1) η(10z)^(-1) η(26z)^(-1) η(30z)^2 η(78z)^2 η(130z)^2 η(390z)^(-1)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(6z)^(-1) η(10z)^(-1) η(26z)^(-1) η(30z)^2 η(78z)^2 η(130z)^2 η(390z)^(-1)` at level 390. -/
abbrev cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_old_390_2 : gamma0CuspForms 390 :=
  gamma0Rescale cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_old_390_2_eq_eta :
    cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_old_390_2 =
      etaQuotientCuspForm 390 sparse![390; 1 => 2, 5 => -1, 9 => -1, 25 => -1, 29 => 2, 77 => 2, 129 => 2, 389 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_old_390_2_first_coeffs :
    first_coeffs 100 cuspForm_195_eta_1p2_3m1_5m1_13m1_15p2_39p2_65p2_195m1_old_390_2 =
    [0, 0, 1, 0, -2, 0, -1, 0, 3, 0, -1, 0, 2, 0, 0, 0, -4, 0, 1, 0,
     2, 0, 0, 0, -3, 0, 0, 0, 1, 0, -1, 0, 4, 0, 1, 0, -3, 0, 4, 0,
     -3, 0, -4, 0, 1, 0, 0, 0, 4, 0, -2, 0, 0, 0, 1, 0, -3, 0, 3, 0,
     2, 0, -2, 0, 0, 0, -3, 0, -4, 0, 2, 0, 5, 0, 4, 0, -9, 0, 0, 0,
     4, 0, 0, 0, 9, 0, -3, 0, -3, 0, -1, 0, -2, 0, -2, 0, -4, 0, 2, 0] := by
  eta_coeff

end WeightTwoCusps
