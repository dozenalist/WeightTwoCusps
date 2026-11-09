module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«195».New.«195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z)^(-1) η(3z)^2 η(5z)^2 η(13z)^2 η(15z)^(-1) η(39z)^(-1) η(65z)^(-1) η(195z)^2`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(5z)^2 η(13z)^2 η(15z)^(-1) η(39z)^(-1) η(65z)^(-1) η(195z)^2` at level 390. -/
abbrev cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_old_390_1 : gamma0CuspForms 390 :=
  gamma0RescaleToLevel cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_old_390_1_eq_eta :
    cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_old_390_1 =
      etaQuotientCuspForm 390 sparse![390; 0 => -1, 2 => 2, 4 => 2, 12 => 2, 14 => -1, 38 => -1, 64 => -1, 194 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_old_390_1_first_coeffs :
    first_coeffs 100 cuspForm_195_eta_1m1_3p2_5p2_13p2_15m1_39m1_65m1_195p2_old_390_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 3, 1, 2,
     0, 4, 1, 2, 0, 3, -2, -2, -3, 3, -4, 0, -2, 3, -8, -2, -2, 4, -5, -1,
     0, -4, -11, -5, -3, 0, -6, 0, -1, -3, -8, -1, 3, 5, 5, -2, 3, -3, -7, 1,
     6, 8, -1, -2, 2, -1, -8, 3, 14, 1, 5, -4, 1, -9, -9, 3, 8, -1, 2, -3,
     -1, 3, 12, 2, 19, -3, 12, -7, 3, 0, 1, 0, 11, 5, -1, -2, 2, 1, 12, -1] := by
  eta_coeff

end WeightTwoCusps
