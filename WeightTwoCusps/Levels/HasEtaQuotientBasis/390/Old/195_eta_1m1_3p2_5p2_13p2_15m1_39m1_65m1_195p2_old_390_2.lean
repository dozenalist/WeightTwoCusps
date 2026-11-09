module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«195».New.«195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(2z)^(-1) η(6z)^2 η(10z)^2 η(26z)^2 η(30z)^(-1) η(78z)^(-1) η(130z)^(-1) η(390z)^2`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(6z)^2 η(10z)^2 η(26z)^2 η(30z)^(-1) η(78z)^(-1) η(130z)^(-1) η(390z)^2` at level 390. -/
abbrev cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_old_390_2 : gamma0CuspForms 390 :=
  gamma0Rescale cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_old_390_2_eq_eta :
    cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_old_390_2 =
      etaQuotientCuspForm 390 sparse![390; 1 => -1, 5 => 2, 9 => 2, 25 => 2, 29 => -1, 77 => -1, 129 => -1, 389 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_old_390_2_first_coeffs :
    first_coeffs 100 cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_old_390_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0,
     0, 0, 4, 0, 1, 0, 2, 0, 0, 0, 3, 0, -2, 0, -2, 0, -3, 0, 3, 0,
     -4, 0, 0, 0, -2, 0, 3, 0, -8, 0, -2, 0, -2, 0, 4, 0, -5, 0, -1, 0,
     0, 0, -4, 0, -11, 0, -5, 0, -3, 0, 0, 0, -6, 0, 0, 0, -1, 0, -3, 0] := by
  eta_coeff

end WeightTwoCusps
