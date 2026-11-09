module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m1_2p1_4p2_5p1_10p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(3z)^(-1) η(6z) η(12z)^2 η(15z) η(30z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z) η(12z)^2 η(15z) η(30z)` at level 480. -/
abbrev cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_480_3 : gamma0CuspForms 480 :=
  gamma0RescaleToLevel cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_480_3_eq_eta :
    cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_480_3 =
      etaQuotientCuspForm 480 sparse![480; 2 => -1, 5 => 1, 11 => 2, 14 => 1, 29 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_480_3_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_480_3 =
    [0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, -2, 0, 0, -4, 0, 0, 0,
     0, 0, -4, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, -3, 0, 0, 0, 0, 0,
     -2, 0, 0, -2, 0, 0, 4, 0, 0, -5, 0, 0, 0, 0, 0, 1, 0, 0, -2, 0,
     0, -2, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
