module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m1_2p1_4p2_5p1_10p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 160

The eta expression is `η(z)^(-1) η(2z) η(4z)^2 η(5z) η(10z)`; see
[the local level table](../../TABLE.md#level-160).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z)^2 η(5z) η(10z)` at level 160. -/
abbrev cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_160_1 : gamma0CuspForms 160 :=
  gamma0RescaleToLevel cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_160_1_eq_eta :
    cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_160_1 =
      etaQuotientCuspForm 160 sparse![160; 0 => -1, 1 => 1, 3 => 2, 4 => 1, 9 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_160_1_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_old_160_1 =
    [0, 1, 1, 1, 2, 0, 0, 1, 0, -1, 1, -2, -4, 0, -4, -1, 0, -2, -3, 0,
     -2, -2, 4, -5, 0, 1, -2, -2, 4, 2, 0, 6, 0, 0, 2, 3, 2, 4, 4, 2,
     0, 0, 0, 9, 0, -2, 4, 1, 0, 3, 1, -6, 4, 0, 0, -2, 0, 4, -2, -4,
     4, 0, -8, -7, 0, -2, 0, -5, -12, -6, -4, 6, 0, -2, 6, 1, -8, -8, 0, -4,
     0, -1, -6, 5, -8, 4, -8, 6, 0, -6, -3, -6, 12, 4, 4, -4, 0, -6, 9, 6] := by
  eta_coeff

end WeightTwoCusps
