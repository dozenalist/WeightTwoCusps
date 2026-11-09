module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1p1_5m1_10p2_11p1_55m1_110p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 220

The eta expression is `η(z) η(5z)^(-1) η(10z)^2 η(11z) η(55z)^(-1) η(110z)^2`; see
[the local level table](../../TABLE.md#level-220).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(5z)^(-1) η(10z)^2 η(11z) η(55z)^(-1) η(110z)^2` at level 220. -/
abbrev cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2_old_220_1 : gamma0CuspForms 220 :=
  gamma0RescaleToLevel cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2_old_220_1_eq_eta :
    cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2_old_220_1 =
      etaQuotientCuspForm 220 sparse![220; 0 => 1, 4 => -1, 9 => 2, 10 => 1, 54 => -1, 109 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2_old_220_1_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2_old_220_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 2, -1, 0, 0, 0, 1, -1,
     1, 1, 0, 0, -3, -1, 0, 0, 0, -1, 1, 1, 1, 0, 1, -1, 3, 0, 0, 0,
     -2, -2, 0, 0, 0, 1, 1, 2, -2, 1, -1, 1, -2, -2, 0, 0, -3, 0, 0, 2,
     -1, 1, 1, 2, 2, 0, 0, -2, 4, -2, 2, -1, 1, 0, 0, 1, -1, 0, -2, -4,
     -1, 0, 0, 0, 1, 1, -2, -2, 1, 5, 1, 0, 0, -2, 0, 0, -1, 0, -2, -1] := by
  eta_coeff

end WeightTwoCusps
