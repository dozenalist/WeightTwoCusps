module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m1_2p1_4p2_5p1_10p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(4z)^(-1) η(8z) η(16z)^2 η(20z) η(40z)`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-1) η(8z) η(16z)^2 η(20z) η(40z)` at level 320. -/
abbrev cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_320_4 : gamma0CuspForms 320 :=
  gamma0Rescale cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_320_4_eq_eta :
    cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_320_4 =
      etaQuotientCuspForm 320 sparse![320; 3 => -1, 7 => 1, 15 => 2, 19 => 1, 39 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_320_4_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_320_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     1, 0, 0, 0, -2, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, -2, 0, 0, 0, 4, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
