module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-1) η(3z)^2 η(4z) η(5z)^2 η(6z) η(10z) η(12z)^(-1) η(15z)^(-1) η(20z)^(-1) η(60z)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z) η(5z)^2 η(6z) η(10z) η(12z)^(-1) η(15z)^(-1) η(20z)^(-1) η(60z)` at level 300. -/
abbrev cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1_old_300_1 : gamma0CuspForms 300 :=
  gamma0RescaleToLevel cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1_old_300_1_eq_eta :
    cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1_old_300_1 =
      etaQuotientCuspForm 300 sparse![300; 0 => -1, 2 => 2, 3 => 1, 4 => 2, 5 => 1, 9 => 1, 11 => -1, 14 => -1, 19 => -1, 59 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1_old_300_1_first_coeffs :
    first_coeffs 100 cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1_old_300_1 =
    [0, 0, 1, 1, 2, 1, 2, 0, -1, -2, -2, -2, -5, -2, -6, -2, -6, 2, 1, 4,
     5, 4, 2, -2, 4, 0, 4, -1, 6, -2, -1, 0, 11, 2, 8, 0, 2, -6, -8, 4,
     -4, 4, -6, 6, -14, 3, 0, 6, 3, -4, 1, -12, -10, -2, 2, -2, -6, -8, -8, -6,
     -2, 0, 12, -4, -2, 0, -2, 6, -2, 10, 6, 0, -1, 4, 8, 1, 20, 0, 2, -4,
     -3, 8, -14, 2, 6, 0, -8, 12, 10, -4, -2, 0, 0, -8, -4, 0, -8, 0, 17, -2] := by
  eta_coeff

end WeightTwoCusps
