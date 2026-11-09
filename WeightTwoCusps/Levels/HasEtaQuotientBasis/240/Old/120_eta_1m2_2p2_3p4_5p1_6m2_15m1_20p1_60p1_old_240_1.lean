module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«120».New.«120_eta_1m2_2p2_3p4_5p1_6m2_15m1_20p1_60p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^4 η(5z) η(6z)^(-2) η(15z)^(-1) η(20z) η(60z)`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_120_eta_1m2_2p2_3p4_5p1_6m2_15m1_20p1_60p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^4 η(5z) η(6z)^(-2) η(15z)^(-1) η(20z) η(60z)` at level 240. -/
abbrev cuspForm_120_eta_1m2_2p2_3p4_5p1_6m2_15m1_20p1_60p1_old_240_1 : gamma0CuspForms 240 :=
  gamma0RescaleToLevel cuspForm_120_eta_1m2_2p2_3p4_5p1_6m2_15m1_20p1_60p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_120_eta_1m2_2p2_3p4_5p1_6m2_15m1_20p1_60p1_old_240_1_eq_eta :
    cuspForm_120_eta_1m2_2p2_3p4_5p1_6m2_15m1_20p1_60p1_old_240_1 =
      etaQuotientCuspForm 240 sparse![240; 0 => -2, 1 => 2, 2 => 4, 4 => 1, 5 => -2, 14 => -1, 19 => 1, 59 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m2_2p2_3p4_5p1_6m2_15m1_20p1_60p1_old_240_1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m2_2p2_3p4_5p1_6m2_15m1_20p1_60p1_old_240_1 =
    [0, 0, 0, 1, 2, 3, 2, 1, 1, 0, 1, 0, 1, -2, -4, -3, -2, 0, 0, 2,
     -1, -2, -2, -1, -4, -6, -2, -2, -6, -2, -3, 0, -3, 4, 10, -1, 2, -2, 4, -4,
     4, 4, 2, -3, -2, 3, -6, 1, 5, 4, 0, 2, 2, 2, -4, 14, 6, 4, -10, -2,
     -2, 0, 8, 1, 10, -6, 2, -1, 10, 0, 4, -2, 1, -4, -6, 7, -4, 0, 6, 6,
     -5, 0, -4, 5, -6, 8, 10, -2, -10, 0, 1, -6, 0, -4, 10, -14, 0, 0, 4, 0] := by
  eta_coeff

end WeightTwoCusps
