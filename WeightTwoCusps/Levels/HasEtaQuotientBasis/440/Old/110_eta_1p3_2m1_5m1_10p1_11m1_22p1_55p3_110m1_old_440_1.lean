module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(z)^3 η(2z)^(-1) η(5z)^(-1) η(10z) η(11z)^(-1) η(22z) η(55z)^3 η(110z)^(-1)`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-1) η(5z)^(-1) η(10z) η(11z)^(-1) η(22z) η(55z)^3 η(110z)^(-1)` at level 440. -/
abbrev cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1_old_440_1 : gamma0CuspForms 440 :=
  gamma0RescaleToLevel cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1_old_440_1_eq_eta :
    cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1_old_440_1 =
      etaQuotientCuspForm 440 sparse![440; 0 => 3, 1 => -1, 4 => -1, 9 => 1, 10 => -1, 21 => 1, 54 => 3, 109 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1_old_440_1_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1_old_440_1 =
    [0, 0, 0, 1, -3, 1, 2, 2, 0, -7, 2, 0, 2, 2, -2, -2, 3, 2, 4, -6,
     -7, 4, 0, 3, -4, 0, -2, 5, 4, 4, -4, -5, 6, 1, -8, -4, 1, -3, 6, 0,
     8, -2, -10, 8, 1, -3, 0, -2, 0, 2, 0, 12, -6, -10, 4, 1, -2, -6, 2, -1,
     4, 0, 8, -2, 3, 2, 2, -15, -8, 3, -2, 1, -2, 10, 12, 1, 2, 2, -12, 2,
     -3, 0, -4, -4, 2, 4, -8, -2, 0, 13, 0, 0, -4, 1, 2, -2, 0, 5, -2, 1] := by
  eta_coeff

end WeightTwoCusps
