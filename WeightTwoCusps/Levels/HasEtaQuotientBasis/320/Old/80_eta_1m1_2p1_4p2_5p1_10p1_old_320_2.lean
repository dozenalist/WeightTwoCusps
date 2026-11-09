module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m1_2p1_4p2_5p1_10p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(2z)^(-1) η(4z) η(8z)^2 η(10z) η(20z)`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z) η(8z)^2 η(10z) η(20z)` at level 320. -/
abbrev cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_320_2 : gamma0CuspForms 320 :=
  gamma0RescaleToLevel cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_320_2_eq_eta :
    cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_320_2 =
      etaQuotientCuspForm 320 sparse![320; 1 => -1, 3 => 1, 7 => 2, 9 => 1, 19 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_320_2_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_320_2 =
    [0, 0, 1, 0, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
     1, 0, -2, 0, -4, 0, 0, 0, -4, 0, -1, 0, 0, 0, -2, 0, -3, 0, 0, 0,
     -2, 0, -2, 0, 4, 0, -5, 0, 0, 0, 1, 0, -2, 0, -2, 0, 4, 0, 2, 0,
     0, 0, 6, 0, 0, 0, 0, 0, 2, 0, 3, 0, 2, 0, 4, 0, 4, 0, 2, 0,
     0, 0, 0, 0, 0, 0, 9, 0, 0, 0, -2, 0, 4, 0, 1, 0, 0, 0, 3, 0] := by
  eta_coeff

end WeightTwoCusps
