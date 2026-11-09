module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m1_2p1_4p2_5p1_10p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(6z)^(-1) η(12z) η(24z)^2 η(30z) η(60z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-1) η(12z) η(24z)^2 η(30z) η(60z)` at level 480. -/
abbrev cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_480_6 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_480_6_eq_eta :
    cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_480_6 =
      etaQuotientCuspForm 480 sparse![480; 5 => -1, 11 => 1, 23 => 2, 29 => 1, 59 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_480_6_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_480_6 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -4, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
